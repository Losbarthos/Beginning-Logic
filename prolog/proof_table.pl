%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proof_table, [
				   		table_init/2,
				   		get_assumption_idx/3,
				   		new_list_index/2,
				   		assume/3,
				   		remove_assumption/4,
				   		table_insert/7,
				   		find_line/4,
				   		write_proof_table/1,
				   		is_proof_table/1
				   		]).

:-use_module(list_helper).
:-use_module(set).
:-use_module(proposition).

:- use_module(library(clpfd)).

% Inits the table with his base assumptions and the conclusion.
table_init(Assumptions, Tbl) :-
	findall(X, (nth1(I, Assumptions, A), X = [[I], I, A, "A", []]), Tbl).

% Stores the Lines in the proof table Tbl of all assumptions which occur in list "Assumptions" in the list Idx.
get_assumption_idx(Assumptions, Tbl, Idx) :-
	findall(I, (A ∈ Assumptions, [[I], I, A, "A", []] ∈ Tbl), Idx).

% Finds the length of the list and increments it by 1
new_list_index(List, NewIndex) :-
    length(List, Length),
    NewIndex is Length + 1.

% remove index of assumption from Table
remove_assumption(Assumption, Line, TblIn, TblOut) :-
	[[I], I, Assumption, "A", []] ∈ TblIn,
	Line = [IA | End],
	delete(IA, I, IR),
	replace(Line, [IR | End], TblIn, TblOut).

table_insert(Assumptions, Premisses, RuleName, Conclusion, Line, TblIn, TblOut) :-
	get_assumption_idx(Assumptions, TblIn, IdxAMax),
	findall(I, (P ∈ Premisses, [IA, I, P, _, _] ∈ TblIn, subset(IA, IdxAMax)), IdxPU),
	findall(IA, (I ∈ IdxPU, [IA, I, _, _, _] ∈ TblIn), AList),
	append(AList, IdxAU1),

	new_list_index(TblIn, I),
	((Conclusion ∈ Assumptions) -> append(IdxAU1, [I], IdxAU) ; IdxAU = IdxAU1), 
	sort(IdxPU, IdxP), sort(IdxAU, IdxA),
	Line = [IdxA, I, Conclusion, RuleName, IdxP],
	append(TblIn, [Line], TblOut).


assume(Assumption, TblIn, TblOut) :-
	table_insert([Assumption], [], "A", Assumption, _, TblIn, TblOut).

% Find the line in table which has conclusion and only uses assumption indexes assumed in Assumptions 
find_line(Assumptions, Conclusion, Tbl, Line) :-
	get_assumption_idx(Assumptions, Tbl, AIdx),
	Line = [AIdx1, _, Conclusion, _, _],
	Line ∈ Tbl,
	subset(AIdx1, AIdx).


write_proof_table(Tbl) :-
	is_proof_table(Tbl),
	nl,
	foreach(X ∈ Tbl, write_term(X, [max_depth(0), nl(true)])).

is_proof_table(Tbl) :-
	findall(X, (X ∈ Tbl,
			    X = [A1, A2, A3, _, A5],
				is_list(A1), is_list(A5),
				is_of_type(positive_integer, A2),
				formula(A3)),
			NewTbl),
	Tbl = NewTbl.