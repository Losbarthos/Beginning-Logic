%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proof_table, [
				   		table_insert/5,
				   		table_init/3,
				   		table_replace/4,
				   		is_proof_table/1,
				   		write_proof_table/1,
				   		define_table/2
				   		]).

:-use_module(list_helper).
:-use_module(set).
:-use_module(graph).
:-use_module(proposition).

:- use_module(library(clpfd)).

% Idea, seperate Table as follows
%	left 	A1 	1 	P1 	R1	P1
%	left 	… 	… 	… 	… 	…
%	left 	An 	m 	Pm 	RM 	[PM]
% 	right 	X1 	I1	C1 	R1 	P1
% 	right 	… 	… 	… 	… 	…
% 	right 	Xo 	Io 	Co 	Ro 	Po

%
%

% checks, if some element is in table
is_in_table(left, Element, Tbl) :-
	Tbl = [Left, _],
	Element ∈ Left.
is_in_table(right, Element, Tbl) :-
	Tbl = [_, Right],
	Element ∈ Right.


% Length of table entries with prefix left or right
length_of(left, TblIn, L) :-
	TblIn = [Left, _],
	length(Left, L).
length_of(right, TblIn, L) :-
	TblIn = [_, Right],
	length(Right, L).

% Gets the Index of the last value of the table represented by the conclusion
get_last_index(Tbl, L) :-
	Tbl = [_, Right],
	last(Right, [_, L, _, _, _]).

get_new_index(left, Tbl, I) :-
	length_of(left, Tbl, L),
	I is L + 1.
get_new_index(right, Tbl, I) :-
	get_last_index(Tbl, N), length_of(right, Tbl, L),
	N #= I + L.

ass_append(A, B, AB) :-
	%when((ground(A);ground(B)), append(A,B,AB)).
	AB = [A, B].
	%append(C, AB).

flattern_assumptions([], []) :- !.
flattern_assumptions(TblIn, TblOut) :- 
	TblIn = [[AA, I, C, R, P] | TblInR],
	flatten(AA, AU), sort(AU,A),
	flattern_assumptions(TblInR, TblOutR),
	append([[A, I, C, R, P]], TblOutR, TblOut).

% Gets some Index of the right Part of the table.
table_idx(left, Tbl, P, Idx) :-
	Tbl = [Left, _],
	Element = [A, I, P, _, _],
	Idx = [A, I],
	Element ∈ Left.

table_idx(right, Tbl, P, Idx) :-
	Tbl = [_, Right],
	Element = [A, I, P, _, _],
	Idx = [A, I],
	Element ∈ Right.

table_append(left, Element, Idx, TblIn, TblIn) :-
	TblIn = [Left, _],
	Element = [A, I, _, _, _],
	Idx = [A, I],
	Element ∈ Left, !.

table_append(left, Element, Idx, TblIn, TblOut) :-
	TblIn = [Left, Right],
	get_new_index(left, TblIn, I),
	Element = [A, I, _, _, _],
	Idx = [A, I],
	append(Left, [Element], LeftOut),
	TblOut = [LeftOut, Right].

table_append(right, Element, Idx, TblIn, TblIn) :-
	TblIn = [Left, _],
	Element = [A, I, _, _, _],
	Idx = [A, I],
	Element ∈ Left, !.

table_append(right, Element, Idx, TblIn, TblIn) :-
	TblIn = [_, Right],
	Element = [A, I, _, _, _],
	Idx = [A, I],
	Element ∈ Right, !.
%table_idx(left, TblIn, Element, Idx).

%table_append(right, Element, Idx, TblIn, TblIn) :-
%	table_idx(right, TblIn, Element, Idx).

table_append(right, Element, Idx, TblIn, TblOut) :-
	TblIn = [Left, Right],
	get_new_index(right, TblIn, I),
	Element = [A, I, _, _, _],
	Idx = [A, I],
	append([Element], Right, RightOut),
	TblOut = [Left, RightOut].

% defines the last index and finishes the table.
define_table(TblIn, TblOut) :-
	append(TblIn, TblB),
	length(TblB, N),
	nth1(N, TblB, X),
	X = [_, N, _, _, _],
	flattern_assumptions(TblB, TblOut).


table_init(Assumptions, Conclusion, Tbl) :-
	findall(X, (nth1(N, Assumptions, A), X = [[N], N, A, "A", []]), AssumptionTable),
	C = [[_, _, Conclusion, _, _]],
	Tbl = [AssumptionTable, C].
	%append(AssumptionTable, C, Tbl).

get_assumptions_idx(Indexes, Tbl, AssumptionIndexes) :-
	Tbl = [Left, Right],
	findall(I, (I ∈ Indexes, [X, I, _, _, _] ∈ Left), ILeft),
	subtract(Indexes, ILeft, IRight),
	findall(X, (I ∈ ILeft, [X, I, _, _, _] ∈ Left), AL),
	findall(X, (I ∈ IRight, [X, I, _, _, _] ∈ Right), AR),
	append(AR, AssumptionIndexesRight),	
	append(AL, AssumptionIndexesLeft),
	union(AssumptionIndexesLeft, AssumptionIndexesRight, AssumptionIndexes).

table_insert("∧I", Assumptions, L ∧ R, TblIn, TblOut) :-
	Assumptions = [L, R],

	C   = [A,     I, L ∧ R, "∧I", [I_L, I_R]],
	P_L = [A_L, I_L, L    , _   , _         ],
	P_R = [A_R, I_R, R    , _   , _         ], 

	table_idx(right, TblIn, L ∧ R, [A, I]),
	table_append(right, P_L, [A_L, I_L], TblIn, TblB),
	table_append(right, P_R, [A_R, I_R], TblB, TblOut),
	ass_append(A_L, A_R, A),
	%get_assumptions_idx([I_L, I_R], TblOut, A),
	is_in_table(right, C, TblOut).

table_insert("↔I", Assumptions, L ↔ R, TblIn, TblOut) :-
	Assumptions = [L → R, R → L],

	C   = [A,     I, L ↔ R, "↔I", [I_L, I_R]],
	P_L = [A_L, I_L, L → R, _   , _         ],
	P_R = [A_R, I_R, R → L, _   , _         ], 

	table_idx(right, TblIn, L ↔ R, [A, I]),
	table_append(right, P_L, [A_L, I_L], TblIn, TblB),
	table_append(right, P_R, [A_R, I_R], TblB, TblOut),
	ass_append(A_L, A_R, A),
	%get_assumptions_idx([I_L, I_R], TblOut, A),
	is_in_table(right, C, TblOut).

table_insert("→I", Assumptions, L → R, TblIn, TblOut) :-
	Assumptions = [L, R],

	table_idx(right, TblIn, L → R, [A_R, I]),
	C = [A_R, I, L → R, "→I", [J, I_R]],
	A = [[J], J, L, "A", []],
	P_R = [A_R, I_R, R, _, _],

	table_append(left, A, [[J], J], TblIn, TblB),
	table_append(right, P_R, [A_R, I_R], TblB, TblOut),

	%get_assumptions_idx([I_R], TblOut, A),
	is_in_table(right, C, TblOut).

table_insert("∧E", Assumptions, L ∧ R, TblIn, TblOut) :-
	Assumptions = [L],

	P_L = [A, J, L, "∧E", [I]],
	C = [A, I, L ∧ R, _, _],
	table_append(left, P_L, [A, J], TblIn, TblB),
	table_append(left, C, [A, I], TblB, TblOut).

table_insert("∧E", Assumptions, L ∧ R, TblIn, TblOut) :-
	Assumptions = [R],

	P_R = [A, J, R, "∧E", [I]],
	C = [A, I, L ∧ R, _, _],
	table_append(left, P_R, [A, J], TblIn, TblB),
	table_append(left, C, [A, I], TblB, TblOut).

table_insert("↔E", Assumptions, L ↔ R, TblIn, TblOut) :-
	Assumptions = [(L → R) ∧ (R → L)],

	P = [A, J, (L → R) ∧ (R → L), "↔E", [I]],
	C = [A, I, L ↔ R, _, _],
	table_append(left, P, [A, J], TblIn, TblB),
	table_append(left, C, [A, I], TblB, TblOut).

table_insert("→E", Assumptions, R, TblIn, TblOut) :-
	Assumptions = [L, L → R],
	
	LR = [A_LR, I_LR, (L → R), _, _],
	P_L = [A_L, I_L, L, _, _],
	P_R = [A, I_R, R, "→E", [I_LR, I_L]],

	table_append(left, LR, [A_LR, I_LR], TblIn, TblB1),
	table_append(right, P_R, [A, I_R], TblB1, TblB2),
	table_append(right, P_L, [A_L, I_L], TblB2, TblOut),
	ass_append(A_L, A_LR, A),
	%get_assumptions_idx([I_LR, I_L], TblOut, A),
	is_in_table(right, P_R, TblOut).

table_insert("∨E", Assumptions, C, TblIn, TblOut) :-
	Assumptions = [L ∨ R, L → C, R → C],

	table_idx(right, TblIn, C, [A, I]),
	X = [_, I_LR, L ∨ R, _, _],
	LC = [A_L, I_L, L → C, _, _],
	RC = [A_R, I_R, R → C, _, _],
	Co = [A, I, C, "∨E", [I_LR, I_L, I_R]],

	table_append(left, X, [A_LR, I_LR], TblIn, TblB1),
	table_append(right, LC, [A_L, I_L], TblB1, TblB2),
	table_append(right, RC, [A_R, I_R], TblB2, TblOut),
	ass_append(A_LR, A_L, A_B),
	ass_append(A_B, A_R, A),
	%get_assumptions_idx([I_LR, I_L, I_R], TblOut, A),
	is_in_table(right, Co, TblOut).

table_insert("∨I", Assumptions, L ∨ R, TblIn, TblOut) :-
	Assumptions = [R],

	table_idx(right, TblIn, L ∨ R, [A, I]),
	P_R = [A, I_R, R, _, _],
	C = [A, I, L ∨ R, "∨I", [I_R]],
	table_append(right, P_R, [A, I_R], TblIn, TblOut),
	%get_assumptions_idx([I_R], TblOut, A),
	is_in_table(right, C, TblOut).

table_insert("¬E", Assumptions, C, TblIn, TblOut) :-
	Assumptions = [¬(C), ⊥(N)],

	table_idx(right, TblIn, C, [A, I]),
	X = [[J], J, ¬(C), "A", []],
	W = [A, I_W, ⊥(N), _, _],
	Co = [A, I, C, "¬E", [J, I_W]],
	table_append(left, X, [[J], J], TblIn, TblB),
	table_append(right, W, [A, I_W], TblB, TblOut),

	%get_assumptions_idx([I_W], TblOut, A),
	is_in_table(right, Co, TblOut).

table_insert("¬I", Assumptions, ¬(C), TblIn, TblOut) :-
	Assumptions = [C, ⊥(N)],

	table_idx(right, TblIn, ¬(C), [A, I]),
	X = [[J], J, C, "A", []],
	W = [A, I_W, ⊥(N), _, _],
	Co = [A, I, ¬(C), "¬I", [J, I_W]],
	table_append(left, X, [[J], J], TblIn, TblB),
	table_append(right, W, [A, I_W], TblB, TblOut),

	%get_assumptions_idx([I_W], TblOut, A),
	is_in_table(right, Co, TblOut).

table_replace(_, _, [], []) :- !.
table_replace(Old, New, TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	table_replace(Old, New, TblNxt, TblNxtOut),
	X = [A, I, Old, R, P],
	Y = [A, I, New, R, P],
	append([Y], TblNxtOut, TblOut).
table_replace(Old, New, TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	table_replace(Old, New, TblNxt, TblNxtOut),
	X = [_, _, C, _, _], not(C = Old),
	append([X], TblNxtOut, TblOut).

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


% Gets the indexes of the assumptions of some propositions named 'Premisses'.
%get_idx([], [], [], [], _, [], []) :- !.
%get_idx(Premisses, Exc, AssumptionIdx, PremissIdx, Tbl, PremissesRemain, ExcRemain) :-
%	Tbl = [Left, _],
%	X ∈ Premisses, X ∉ Exc,
%	Premisses = [X | PremissesNxt],
%	L = [_, AIdx, Idx, X, _, _],
%	L ∈ Left,
%	get_idx(PremissesNxt, Exc, AssumptionIdxNxt, PremissIdxNxt, Tbl, PremissesRemain, ExcRemain),
%	union(AIdx, AssumptionIdxNxt, AssumptionIdx_), sort(AssumptionIdx_, AssumptionIdx),
%	union([Idx], PremissIdxNxt, PremissIdx_), sort(PremissIdx_, PremissIdx), !.
%get_idx(Premisses, Exc, AssumptionIdx, PremissIdx, Tbl, PremissesRemain, ExcRemain) :-
%	Tbl = [Left, _],
%	X ∈ Premisses, X ∈ Exc,
%	Premisses = [X | PremissesNxt],
%	L = [_, _, Idx, X, _, _],
%	L ∈ Left,
%	get_idx(PremissesNxt, Exc, AssumptionIdx, PremissIdxNxt, Tbl, PremissesRemain, ExcRemain),
%	union([Idx], PremissIdxNxt, PremissIdx_), sort(PremissIdx_, PremissIdx), !.
%get_idx(Premisses, Exc, AssumptionIdx, PremissIdx, Tbl, PremissesRemain, ExcRemain) :-
%	Tbl = [Left, _],
%	X ∈ Premisses, X ∉ Exc,
%	Premisses = [X | PremissesNxt],
%	L = [_, AIdx, Idx, X, _, _],
%	L ∉ Left,
%	get_idx(PremissesNxt, Exc, AssumptionIdxNxt, PremissIdxNxt, Tbl, PremissesB, ExcRemain),
%	union([X], PremissesB, PremissesRemain), !.
%get_idx(Premisses, Exc, AssumptionIdx, PremissIdx, Tbl, PremissesRemain, ExcRemain) :-
%	Tbl = [Left, _],
%	X ∈ Premisses, X ∈ Exc,
%	Premisses = [X | PremissesNxt],
%	L = [_, AIdx, Idx, X, _, _],
%	L ∉ Left,
%	get_idx(PremissesNxt, Exc, AssumptionIdxNxt, PremissIdxNxt, Tbl, PremissesB, ExcB),
%	union([X], PremissesB, PremissesRemain), 
%	union([X], ExcB, ExcRemain), !.

%append_rule(left, Assumptions, Premisses, Rule, Conclusion, TblIn, TblOut) :-
%	subtract(Premisses, Assumptions, Exc),
%	get_idx(Assumptions, Exc, AIdx, PIdx, TblIn, [], []),
%	C = [left, AIdx, _, Conclusion, Rule, PIdx],
%	append(left, C, TblIn, TblOut).
%append_rule(right, Assumptions, Premisses, Rule, Conclusion, TblIn, TblOut) :-
%	subtract(Premisses, Assumptions, Exc),
%	get_idx(Assumptions, Exc, AIdx, PIdx, TblIn, AssumptionsRemain, ExcRemain),





% finds the first value with prefix right. This value is the direct successor of the last value with prefix left.
%find_first(right, First, Tbl, N) :-
%	nth1(N, Tbl, X),
%	NN #= N + 1,
%	(X = [left, _, _, _, _, _]
%	->
%	find_first(right, First, Tbl, NN)
%	; First = X).
% finds the first value with prefix left. This value is the direct ancestor of the last value with prefix right.
%find_last(left, Last, Tbl, N, N) :-
%	length(Tbl, N), 
%	nth1(N, Tbl, X),
%	X = [left | _],
%	Last = X, !.
%find_last(left, Last, Tbl, N, M) :-
%	NP1 #= N + 1,
%	nth1(NP1, Tbl, Y),
%	nth1(N, Tbl, X),
%	((nth1(1, X, left), nth1(1, Y, right))
%	->
%	Last = X, N = M;
%	find_last(left, Last, Tbl, NP1, M)).

/*insert_after(Element, TblIn, TblOut) :-
	find_last(left, Last, TblIn, 1, M),
	MM #= M + 1,
	Element = [left, _, MM, _, _, _],
	insert_after(TblIn, Last, Element).

insert_front_of(Element, TblIn, TblOut) :-
	find_first(right, First, TblIn, 1),
	length_of(right, TblIn, N),
	get_last_index(TblIn, L),
	L #= I + N - 1
	Element = [right, _, I, _, _, _],
	insert_after(TblIn, Last, Element).


% defines the last index and finishes the table.
define_table(Tbl) :-
	length(Tbl, N),
	nth1(N, Tbl, X),
	X = [right, _, N, _, _, _].



add_conclusion(Assumptions, Premisses, Rule, Conclusion, TblIn, TblOut) :-
	subset(Assumptions, Premisses),
	get_assumption_idx(Assumptions, AIdx, TblIn),
	get_premiss_idx(Premisses, PIdx, AIdx, TblIn),
	C = [left, AIdx, _, Conclusion, Rule, PIdx],
	insert_after(C, TblIn, TblOut).

add_premisses(Assumptions, Premisses, Rule, Conclusion, TblIn, TblOut) :-



new_premiss_lines([], _, [], [], []) :- !.
new_premiss_lines(Premisses, I, Prefix, PremissIndexes, AssumptionIndexes) :-
	Premisses = [P1 | PremissesBack], length(Premisses, N),
	X1 = [right, A, J1, P1, _, _],
	I #= J1 + N,
	new_premiss_lines(PremissesBack, I, PrefixBack, PremissIndexesBack, AssumptionIndexesBack),
	Prefix = [X1 | PrefixBack],
	PremissIndexes = [J1 | PremissIndexesBack], 
	AssumptionIndexes = [A | AssumptionIndexesBack], !.

old_premiss_lines(_, [], [], [], []) :- !.
old_premiss_lines(Tbl, Premisses, OldPremisses, OldPremissIndexes, OldPremissAssumptions) :-
	Premisses = [P | NextPremisses],
	X = [left, A, I, P, _, _], X ∈ Tbl,
	old_premiss_lines(Tbl, NextPremisses, NextOldPremisses, NextOldPremissIndexes, NextOldPremissAssumptions),
	append(A, NextOldPremissAssumptions, OldPremissAssumptions),
	append([I], NextOldPremissIndexes, OldPremissIndexes),
	append(X, NextOldPremisses, OldPremisses), !.
old_premiss_lines(Tbl, Premisses, OldPremisses, OldPremissIndexes, OldPremissAssumptions) :-
	Premisses = [P | NextPremisses],
	X = [left, _, _, P, _, _], X ∉ Tbl,
	old_premiss_lines(Tbl, NextPremisses, OldPremisses, OldPremissIndexes, OldPremissAssumptions), !.

table_init(Assumptions, Conclusion, Tbl) :-
	findall(X, (nth1(N, Assumptions, A), X = [left, [N], N, A, "A", []]), AssumptionTable),
	C = [[right, _, _, Conclusion, _, _]],
	append(AssumptionTable, C, Tbl).
table_assume(A, TblIn, TblOut) :-
	find_last(left, Last, TblIn, 1, N),
	NN #= N + 1,
	X = [left, [NN], NN, A, "A", []],
	insert_after(TblIn, [X], Last, TblOut).


remove_from_table(_, [], []) :- !.
remove_from_table(Remove, TblIn, TblOut) :-
	TblIn = [X | TblBack],
	X = Remove,
	remove_from_table(Remove, TblBack, TblOut), !.
remove_from_table(Remove, TblIn, TblOut) :-
	TblIn = [X | TblBack],
	remove_from_table(Remove, TblBack, TblBackOut),
	append([X], TblBackOut, TblOut).

insert_at_left_without_remove_right(Premisses, Conclusion, Rule, TblIn, TblOut) :-
	find_last(left, Last, TblIn, 1, I),
	J #= I + 1, 
	nth1(I, TblIn, Last),
	New = [left, AssumptionIdx, J, Conclusion, Rule, PremissIdx],
	old_premiss_lines(TblIn, Premisses, _, PremissIdx, AssumptionIdx),
	insert_after(TblIn, [New], Last, TblOut).


table_insert(right, Premisses, Conclusion, Rule, TblIn, TblOut) :-
	find_first(right, First, TblIn, 1),
	First = [right, _, I, _, Rule, _],
	C ∈ TblIn, C = [right, AssumptionIdx, _, Conclusion, Rule, PremissIdx],
	old_premiss_lines(TblIn, Premisses, PremissesProved, PremissIdxProved, AssumptionIdxProved),
	subtract(Premisses, PremissesProved, PremissesNotProved),
	new_premiss_lines(PremissesNotProved, I, PremissesNotProved, PremissIdxNotProved, AssumptionIdxNotProved),
	union(PremissIdxProved, PremissIdxNotProved, PremissIdx),
	union(AssumptionIdxProved, AssumptionIdxNotProved, AssumptionIdx),
	insert_front_of(TblIn, PremissesNotProved, First, TblOut).
table_insert(left, Premisses, Conclusion, Rule, TblIn, TblOut) :-
	New = [right, _, _, Conclusion, Rule, _],
	New ∈ TblIn,	
	insert_at_left_without_remove_right(Premisses, Conclusion, Rule, TblIn, Tbl),
	remove_from_table(New, Tbl, TblOut), !.
table_insert(left, Premisses, Conclusion, Rule, TblIn, TblOut) :-
	insert_at_left_without_remove_right(Premisses, Conclusion, Rule, TblIn, TblOut).
	





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
	once(proof_graph_to_table(graph(A, []), graph(V, E), TblIn, Tbl, [])).*/



