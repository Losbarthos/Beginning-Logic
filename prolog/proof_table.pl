%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proof_table, [
				   		proof_table/2,
				   		is_proof_table/1,
				   		write_proof_table/1
				   		]).


:-use_module(graph).
:-use_module(proposition).

:- use_module(library(clpfd)).


% Gets all the assumptions into the table.
import_assumptions(A, [], _) :-
	length(A, N), N = 0.
import_assumptions(A, Tbl, Index) :-
	length(A, N), N = 1, A = [A0], Tbl = [[[Index], Index, A0, "A", []]].
import_assumptions(A, Tbl, Index) :-
	length(A, N), N > 1, A = [A0 | A1], Tbl_0 = [[[Index], Index, A0, "A", []]],
	IndexNext #= Index + 1, 
	import_assumptions(A1, Tbl_1, IndexNext),
	append(Tbl_0, Tbl_1, Tbl).
import_assumptions(A, Tbl) :-
	import_assumptions(A, Tbl, 1).



% For organisation of all the other rules.

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "∧I", Conclusion = (L ∧ R),
	L ∈ Base, R ∈ Base, Origin = [L, R].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "↔I", Conclusion = (L ↔ R),
	(L → R) ∈ Base, (R → L) ∈ Base, Origin = [(L → R), (R → L)].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "→I", Conclusion = (L → R),
	L ∈ Base, R ∈ Base, Origin = [L, R].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "∧E", Conclusion = L,
	(L ∧ R) ∈ Base, Origin = [L ∧ R].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "∧E", Conclusion = R,
	(L ∧ R) ∈ Base, Origin = [L ∧ R].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "↔E", Conclusion = ((L → R) ∧ (R → L)),
	(L ↔ R) ∈ Base, Origin = [L ↔ R].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "→E", Conclusion = R,
	L ∈ Base, (L → R) ∈ Base, Origin = [L, (L → R)].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "∨E", Conclusion = C,
	(L ∨ R) ∈ Base, (L → C) ∈ Base, (R → C) ∈ Base, 
	Origin = [L ∨ R, L → C, R → C].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "∨I", Conclusion = (L ∨ _),
	L ∈ Base, Origin = [L].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "∨I", Conclusion = (_ ∨ R),
	R ∈ Base, Origin = [R].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "¬E", Conclusion = C,
	¬(C) ∈ Base, (X ∧ ¬(X)) ∈ Base, Origin = [¬(C), (X ∧ ¬(X))].

origin_class(Origin, Base, Conclusion, Rule) :-
	Rule = "¬I", Conclusion = ¬(C),
	C ∈ Base, (X ∧ ¬(X)) ∈ Base, Origin = [C, (X ∧ ¬(X))].

% Edge is a list of edges [edge(Xi, Yi, Ri)], Origin is ist list of all Xi with Yi = C and Ri = R.
origin(Edges, C, R, Origin, EOrigin) :-
	findall(X, (edge(X, C, R) ∈ Edges), O),
	origin_class(OriginList, O, C, R),
	findall(edge(X, C, R), (X ∈ OriginList), EO),
	sort(OriginList, Origin), sort(EO, EOrigin).

get_next_used(E, C, EOrigin, EUsed, VUNxt) :-
	findall(X, (edge(X, C, _) ∈ E), O),
	findall(edge(X, C, _), (X ∈ O), EO),
	union(EUsed, EOrigin, EUsedNxt),
	subset(EO, EUsedNxt), VUNxt = [C], !.
get_next_used(_, _, _, _, []).


% Gets the assumptions of the premisses in Origin 
origin_assumptions(TblIn, Origin, Assumptions) :-
	findall(I, (O ∈ Origin, [I, O, _, _, _] ∈ TblIn), AList), 
	append(AList, AssumptionList), sort(AssumptionList, Assumptions).
assumptions(TblIn, _, R, Origin, Assumptions) :-
	R ∉ ["¬I", "¬E", "→I"],
	origin_assumptions(TblIn, Origin, Assumptions).
assumptions(TblIn, C, R, Origin, Assumptions) :-
	R = "¬I", C = ¬(D),
	findall(I, ([_, I, D, "A", _] ∈ TblIn), Except),
	origin_assumptions(TblIn, Origin, OAssumptions),
	subtract(OAssumptions, Except, Assumptions).
assumptions(TblIn, C, R, Origin, Assumptions) :-
	R = "¬E", 
	findall(I, ([_, I, ¬(C), "A", _] ∈ TblIn), Except),
	origin_assumptions(TblIn, Origin, OAssumptions),
	subtract(OAssumptions, Except, Assumptions).
assumptions(TblIn, C, R, Origin, Assumptions) :-
	R = "→I", C = (A → _),
	findall(I, ([_, I, A, "A", _] ∈ TblIn), Except),
	origin_assumptions(TblIn, Origin, OAssumptions),
	subtract(OAssumptions, Except, Assumptions).
assumptions(TblIn, C, R, Origin, Assumptions) :-
	R = "→E", C = (A → _),
	findall(I, ([_, I, A, "A", _] ∈ TblIn), Except),
	origin_assumptions(TblIn, Origin, OAssumptions),
	subtract(OAssumptions, Except, Assumptions).

premisses(TblIn, C, R, Origin, Premisses) :-
	R = "→I", C = (A → B),
	A ∈ Origin, [_, I1, A, "A", _] ∈ TblIn,
	B ∈ Origin, [Assumptions, I2, B, _, _] ∈ TblIn,
	I1 ∈ Assumptions,
	PremissList = [I1, I2], sort(PremissList, Premisses), !.
premisses(TblIn, _, R, Origin, Premisses) :-
	R = "→E", Origin = [O1, O2],
	findall(X, [_, X, O1, _, _] ∈ TblIn, L1),
	findall(X, [_, X, O2, _, _] ∈ TblIn, L2),
	sort(0,@>,L1,S1), sort(0,@>,L2,S2),
	I1 ∈ S1, I2 ∈ S2,
	PremissList = [I1, I2], sort(PremissList, Premisses), !.
premisses(TblIn, _, R, Origin, Premisses) :-
	not(R = "→I"),
	findall(I, (O ∈ Origin, [_, I, O, _, _] ∈ TblIn), PremissList), sort(PremissList, Premisses).


% appends some Rule with Premisses in Origin, C as Conclusion, R as RuleName at TblIn and stores the result into TblOut.
append_rule(TblIn, TblOut, Index, C, Rule, Origin) :-
	premisses(TblIn, C, Rule, Origin, Premisses),
	assumptions(TblIn, C, Rule, Premisses, Assumptions),
	Line = [[Assumptions, Index, C, Rule, Premisses]],
	append(TblIn, Line, TblOut).

append_assumption(TblIn, TblOut, Index, A) :-
	Line = [[[Index], Index, A, "A", []]],
	append(TblIn, Line, TblOut).

append_if_not_empty(VUsedLst, _, VUsedLstNew) :- 
	VUsedLst = [], VUsedLstNew = [], !.
append_if_not_empty(VUsedLst, [C], VUsedLstNew) :-
	union(VUsedLst, [C], VUsedLstNew).

proof_graph_to_table(graph(VUsed, EUsed), graph(V, E), TblIn, TblOut, _) :-	
	subset(V, VUsed), subset(E, EUsed), TblOut = TblIn, !. 
proof_graph_to_table(graph(VUsed, EUsed), graph(V, E), TblIn, TblOut, VUsedLst) :-	
	union(VUsed, VUsedLst, VUsedTmp),
	length(TblIn, I), Index #= I + 1, C ∈ V, C ∉ VUsedTmp,
	edge(_, C, R) ∈ E, 
	origin(E, C, R, Origin, EOrigin),
	get_next_used(E, C, EOrigin, EUsed, VUNxt),
	intersection(EOrigin, EUsed, []),
	subset(Origin, VUsedTmp),
	append_rule(TblIn, TblNxt, Index, C, R, Origin),
	union(VUsed, VUNxt, VUsedNxt), 
	union(EUsed, EOrigin, EUsedNxt),
	append_if_not_empty(VUsedLst, [C], VUsedLstNew),
	proof_graph_to_table(graph(VUsedNxt, EUsedNxt), graph(V, E), TblNxt, TblOut, VUsedLstNew), !.
proof_graph_to_table(graph(VUsed, EUsed), graph(V, E), TblIn, TblOut, VUsedLst) :- 
	length(TblIn, I), Index #= I + 1, C ∈ V, C ∉ (VUsed ∪ [VUsedLst]),
	edge(X, C, _) ∈ E,
	edge(C, X, _) ∈ E,
	edge(C, _, "→I") ∈ E,
	not([_, _, C, "A", _] ∈ TblIn),
	append_assumption(TblIn, TblNxt, Index, C),
	%union(VUsed, [C], VUsedNxt), 
	proof_graph_to_table(graph(VUsed, EUsed), graph(V, E), TblNxt, TblOut, [C]).


get_assumptions(graph(_, E), Assumptions) :-
	findall(X, (edge(X, _, _) ∈ E, edge(_, X, _) ∉ E), AList), sort(AList, Assumptions).
	%findall(X, (edge(_, X → _, "→I") ∈ E), AFromImp),
	%findall(X, (edge(¬(X), X, "¬E") ∈ E), AFromNegE),
	%findall(X, (edge(X, ¬(X), "¬I") ∈ E), AFromNegI),
	%union(AFromNegE, AFromNegI, AFromNeg),
	%union(AFromNeg, AFromImp, AFromRules),
	%union(AList, AFromRules, A), sort(A, Assumptions).

proof_table(graph(V, E), Tbl) :-
	get_assumptions(graph(V, E), A),
	import_assumptions(A, TblIn), 
	once(proof_graph_to_table(graph(A, []), graph(V, E), TblIn, Tbl, [])).

is_proof_table(Tbl) :-
	findall(X, (X ∈ Tbl,
			    X = [A1, A2, A3, _, A5],
				is_list(A1), is_list(A5),
				is_of_type(positive_integer, A2),
				formula(A3)),
			NewTbl),
	Tbl = NewTbl.


write_proof_table(Tbl) :-
	is_proof_table(Tbl),
	nl,
	foreach(X ∈ Tbl, write_term(X, [max_depth(0), nl(true)])).