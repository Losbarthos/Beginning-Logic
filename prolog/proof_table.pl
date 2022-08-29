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

% E is a list of edges [edge(Xi, Yi, Ri)], Origin is ist list of all Xi with Yi = C and Ri = R.
origin(Edges, C, R, Origin) :-
	findall(X, (edge(X, C, R) ∈ Edges), OriginList),
	sort(OriginList, Origin).

% Gets the assumptions of the premisses in Origin 
origin_assumptions(TblIn, Origin, Assumptions) :-
	findall(I, (O ∈ Origin, [I, _, O, _, _] ∈ TblIn), AList), 
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

% appends some Rule with Premisses in Origin, C as Conclusion, R as RuleName at TblIn and stores the result into TblOut.
append_rule(TblIn, TblOut, Index, C, Rule, Origin) :-
	assumptions(TblIn, C, Rule, Origin, Assumptions),
	findall(I, (O ∈ Origin, [_, I, O, _, _] ∈ TblIn), PremissList),
	sort(PremissList, Premisses),
	Line = [[Assumptions, Index, C, Rule, Premisses]],
	append(TblIn, Line, TblOut).

proof_graph_to_table(Used, graph(V, _), TblIn, TblOut) :-	
	subset(V, Used), TblOut = TblIn, !. 
proof_graph_to_table(Used, graph(V, E), TblIn, TblOut) :-	
	length(TblIn, I), Index #= I + 1, C ∈ V, C ∉ Used,
	edge(_, C, R) ∈ E, 
	origin(E, C, R, Origin),
	subset(Origin, Used),
	append_rule(TblIn, TblNxt, Index, C, R, Origin),
	union(Used, [C], UsedNxt), 
	proof_graph_to_table(UsedNxt, graph(V, E), TblNxt, TblOut).





proof_table(graph(V, E), Tbl) :-
	findall(X, (edge(X, _, _) ∈ E, edge(_, X, _) ∉ E), AList), sort(AList, A),
	import_assumptions(A, TblIn), 
	once(proof_graph_to_table(A, graph(V, E), TblIn, Tbl)).

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