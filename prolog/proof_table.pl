%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

%:- module(proof_table, [
%				   		proof_table/2,
%				   		is_proof_table/1,
%				   		write_proof_table/1
%				   		]).

:-use_module(list_helper).
:-use_module(set).
:-use_module(graph).
:-use_module(proposition).

:- use_module(library(clpfd)).



find_first(right, First, Tbl, N) :-
	nth1(N, Tbl, X),
	(X = [left, _, _, _, _, _]
	->
	find_first(right, First, Tbl, N+1)
	; First = X).


find_last(left, Last, Tbl, N, M) :-
	length(Tbl, N), 
	nth1(N, Tbl, X),
	X = [left, _, _, _, _, _],
	Last = X, 
	M = N, !.
find_last(left, Last, Tbl, N, M) :-
	nth1(N+1, Tbl, Y),
	nth1(N, Tbl, X),
	((X = [left, _, _, _, _, _],
	  Y = [right, _, _, _, _, _])
	->
	Last = X;
	find_last(left, Last, Tbl, N+1, M)).


new_premiss_lines([], _, [], []) :- !.
new_premiss_lines(Premisses, I, Prefix, PremissIndexes, AssumptionIndexes) :-
	Premisses = [P1 | PremissesBack], length(Premisses, N),
	X1 = [right, A, J1, P1, _, _],
	I #= J1 + N,
	premiss_lines(PremissesBack, I, PrefixBack, PremissIndexesBack, AssumptionIndexesBack),
	Prefix = [X1 | PrefixBack],
	PremissIndexes = [J1 | PremissIndexesBack], 
	AssumptionIndexes = [A | AssumptionIndexesBack]!.

old_premiss_lines(_, [], [], [], []) :- !.
old_premiss_lines(Tbl, Premisses, OldPremisses, OldPremissIndexes, OldPremissAssumptions) :-
	Premisses = [P | NextPremisses],
	X = [left, A, I, P, _, _], X ∈ Tbl,
	old_premiss_lines(Tbl, NextPremisses, NextOldPremisses, NextOldPremissIndexes, NextOldPremissAssumptions),
	append(A, NextOldPremissAssumptions, OldPremissAssumptions),
	append(I, NextOldPremissIndexes, OldPremissIndexes),
	append(X, NextOldPremisses, OldPremisses).

table_init(Assumptions, Conclusion, Tbl) :-
	findall(X, (nth1(N, Assumptions, A), X = [[left, [N], N, A, "A", []]]), AssumptionTable),
	C = [[right, _, _, Conclusion, _, _]],
	append(AssumptionTable, C, Tbl).

table_insert(right, Premisses, Conclusion, Rule, TblIn, TblOut) :-
	find_first(right, First, TblIn, 1),
	First = [right, _, I, _, Rule, _],
	C ∈ TblIn, C = [right, AssumptionIdx, _, Conclusion, Rule, PremissIdx],
	old_premiss_lines(TblIn, Premisses, _, PremissIdxProved, AssumptionIdxProved),
	new_premiss_lines(PremissesNotProved, I, PremissesNotProved, PremissIdxNotProved),
	union(PremissIdxProved, PremissIdxNotProved, PremissIdx),
	union(AssumptionIdxProved, , AssumptionIdx)
	insert_front_of(TblIn, PremissesNotProved, First, TblOut).

table_insert(left, Premisses, Conclusion, Rule, TblIn, TblOut) :-
	find_last(left, Last, TblIn, I),
	J is I + 1, 
	nth1(I, TblIn, First)
	New = [left, AssumptionIdx, J, Conclusion, Rule, PremissIdx],
	old_premiss_lines(TblIn, Premisses, _, PremissIdx, AssumptionIdx),
	insert_after(TblIn, [New] First, TblOut).


table_replace(_, _, [], []) :- !.
table_replace(Old, New, TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	table_replace(Old, New, TblNxt, TblNxtOut),
	X = [_, _, _, Old, _, _],
	Y = [_, _, _, New, _, _],
	append([Y], TblNxtOut, TblOut).

table_no_prefix([], []) :- !.
table_no_prefix(TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	table_no_prefix(TblNxt, TblNxtOut),
	X = [_, E1, E2, E3, E4, E5],
	Y = [E1, E2, E3, E4, E5],
	append([Y], TblNxtOut, TblOut).


test(T) :-
	set_prolog_flag(answer_write_options,[max_depth(0)]),
	table_init([], p → q, T0),
	table_insert(right, [p, q], p → q, "→E", T0, T),
	%table_insert(right, [o, p], p, "→E", T1, T),
	length(T, N),
	nth1(N, T, [right, _, X, _, _, _]),
	X #= N.





%
% old stuff for deletion
%



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
	R = "→I", C = (A → B), A ∈ Origin, B ∈ Origin, length(Origin, 2),
	findall(X, [_, X, A, "A", _] ∈ TblIn, L1),
	L1 = [I1],
	findall(X, ([Assumptions, X, B, _, _] ∈ TblIn, I1 ∈ Assumptions), L2),
	sort(0,@>,L2,S2), I2 ∈ S2, Premisses = [I1, I2], !.
premisses(TblIn, _, R, Origin, Premisses) :-
	R = "∨I", Origin = [A],
	findall(X, [_, X, A, _, _] ∈ TblIn, L1),
	sort(0,@>,L1,S1), I1 ∈ S1, Premisses = [I1], !.
premisses(TblIn, _, R, Origin, Premisses) :-
	R = "→E", Origin = [O1, O2],
	findall(X, [_, X, O1, _, _] ∈ TblIn, L1),
	findall(X, [_, X, O2, _, _] ∈ TblIn, L2),
	sort(0,@>,L1,S1), sort(0,@>,L2,S2),
	I1 ∈ S1, I2 ∈ S2,
	PremissList = [I1, I2], sort(PremissList, Premisses), !.
premisses(TblIn, _, R, Origin, Premisses) :-
	not(R = "→I"), not(R = "∨I"), not(R="→E"),
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

% for checking, if origin is in Table
is_in_table(Origin, TblIn) :-
	findall(X, [_, _, X, _, _] ∈ TblIn, Base),
	subset(Origin, Base).

proof_graph_to_table(graph(VUsed, EUsed), graph(V, E), TblIn, TblOut, _) :-	
	subset(V, VUsed), subset(E, EUsed), TblOut = TblIn, !. 
proof_graph_to_table(graph(VUsed, EUsed), graph(V, E), TblIn, TblOut, VUsedLst) :-	
	union(VUsed, VUsedLst, VUsedTmp),
	length(TblIn, I), Index #= I + 1, C ∈ V, C ∉ VUsedTmp,
	edge(_, C, R) ∈ E, 
	origin(E, C, R, Origin, EOrigin),
	get_next_used(E, C, EOrigin, EUsed, VUNxt),
	intersection(EOrigin, EUsed, []),
	is_in_table(Origin, TblIn),
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