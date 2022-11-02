%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proof_table, [
				   		table_insert/6,
				   		table_init/3,
				   		table_replace/4,
				   		table_replace_T/4,
				   		is_proof_table/1,
				   		write_proof_table/1,
				   		complete_subproof/3,
				   		define_table/2
				   		]).

:-use_module(list_helper).
:-use_module(no_unify).
:-use_module(set).
:-use_module(graph).
:-use_module(proposition).

:- use_module(library(clpfd)).

% Inits the table with his base assumptions and the conclusion.
table_init(Assumptions, Conclusion, Tbl) :-
	findall(X, (nth1(N, Assumptions, A), X = [[N], N, A, "A", []]), AssumptionTable),
	C = [[_, _, Conclusion, _, _]],
	Tbl = [AssumptionTable, C].

list_reduce(_, [], []) :- !.
list_reduce(Min, ListIn, ListOut) :-
	ListIn = [First | Rest],
	First < Min,
	list_reduce(Min, Rest, RestOut),
	append([First], RestOut, ListOut), !.
list_reduce(Min, ListIn, ListOut) :-
	ListIn = [First | Rest],
	FirstM is First - 1,
	list_reduce(Min, Rest, RestOut),
	append([FirstM], RestOut, ListOut).


tbl_reduce_idx_by_one(TblIn, TblOut) :-
	TblIn = [First | _],
	First = [_, Min, _, _, _],
	findall(X,(
				Y ∈ TblIn, 
				Y = [AIn, I, C, R, PIn],
				J is I - 1,
				list_reduce(Min, AIn, AOut), list_reduce(Min, PIn, POut),
				X = [AOut, J, C, R, POut]
			  ), 
			TblOut).

% Saves the index lines in Used for which:
% 	the index of Element occurs in further Premisses of Tbl elements.
get_usedlines(_, [], []) :- !.
get_usedlines(Element, Tbl, Used) :-
	Tbl = [First | Rest],
	Element = [_, I, _, _, _],
	First = [_, J, _, _, P],
	I ∈ P,
	get_usedlines(Element, Rest, UsedNxt),
	append([J], UsedNxt, Used), !.
get_usedlines(Element, Tbl, Used) :-
	Tbl = [_ | Rest],
	get_usedlines(Element, Rest, Used).


% Removes the useless entries of TblIn (means, they are not used in any premiss of further lines)
% and stores it in TblOut.
% If their could be some more useless entries, the argument Repead gets true, otherwise it gets false.
remove_useless([First], [First], false) :- !.
remove_useless(TblIn, TblOut, true) :-
	TblIn =[First | Rest],
	get_usedlines(First, Rest, Used), Used = [],
	remove_useless(Rest, RestOut, _),
	tbl_reduce_idx_by_one(RestOut, TblOut), !.
remove_useless(TblIn, TblOut, Repead) :-
	TblIn =[First | Rest],
	remove_useless(Rest, TblB, Repead),
	append([First], TblB, TblOut).


remove_useless(TblIn, TblOut) :- 
	remove_useless(TblIn, TblB, true),
	remove_useless(TblB, TblOut),!.
remove_useless(TblIn, TblIn) :- 
	remove_useless(TblIn, TblIn, false).


%
% Predicates work with assumptions
%

% gets the base assumption indexes Index based on Tbl of the assumption lists Assumptions.
assumption_index(Assumptions, Index, Tbl) :-
	Tbl = [Pre, _],
	findall(I, (A ∈ Assumptions, [[I], I, A, "A", _] ∈ Pre), IndexU),
	sort(IndexU, Index).

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


table_append(_, Element, PRight, PRight, TblIn, TblIn) :-
	TblIn = [Left, _],
	Element ∈ Left.

table_append(_, Element, PRight, NewRight, TblIn, TblIn) :-
	Element ∈ PRight,
	after_and_before(Element, PRight, NewRight, _).

table_append(left, Element, PRight, PRight, TblIn, TblOut) :-
	TblIn = [Left, Right],
	get_new_index(left, TblIn, I),
	Element = [_, I, _, _, _],
	append(Left, [Element], LeftOut),
	TblOut = [LeftOut, Right].

table_append(right, Element, _, [], TblIn, TblOut) :-
	TblIn = [Left, Right],
	%get_new_index(right, TblIn, I),
	%Element = [_, I, _, _, _],
	append([Element], Right, RightOut),
	%append([Element], PRight, NewRight),
	TblOut = [Left, RightOut].

table_insert("∧I", Assumptions, Premisses, L ∧ R, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L, R],

	C   = [AIdx,	_, L ∧ R, "∧I", [I_L, I_R]],
	P_L = [   _,  I_L, L    , _   , _         ],
	P_R = [   _,  I_R, R    , _   , _         ], 

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(right, P_L, Right1, Right2, TblB0, TblB1),
	table_append(right, P_R, Right2, _, TblB1, TblOut))).

table_insert("↔I", Assumptions, Premisses, L ↔ R, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L → R, R → L],

	C   = [AIdx,   _, L ↔ R, "↔I", [I_L, I_R]],
	P_L = [   _, I_L, L → R, _   , _         ],
	P_R = [   _, I_R, R → L, _   , _         ], 

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(right, P_L, Right1, Right2, TblB0, TblB1),
	table_append(right, P_R, Right2, _, TblB1, TblOut))).

table_insert("→I", Assumptions, Premisses, L → R, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L, R],


	C   = [AIdx , _  , L → R, "→I", [J, I_R]],
	X   = [[J]  , J  , L    , "A" , []],
	P_R = [    _, I_R, R    , _   , _],

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, P_R, Right2, _, TblB1, TblOut))).

table_insert("∧E", Assumptions, Premisses, L, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L ∧ R],

	P_LR = [   _, I, L ∧ R,    _, _],
	C    = [AIdx, _, L    , "∧E", [I]],

	TblIn = [_, Right0],
	
	once((table_append(left, P_LR, Right0, Right1, TblIn, TblB1),
	table_append(left, C, Right1, _, TblB1, TblOut))).

table_insert("∧E", Assumptions, Premisses, R, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L ∧ R],
	
	P_LR = [   _, I, L ∧ R,    _, _],
	C =    [AIdx, _, R    , "∧E", [I]],

	TblIn = [_, Right0],
	
	once((table_append(left, P_LR, Right0, Right1, TblIn, TblB1),
	table_append(left, C, Right1, _, TblB1, TblOut))).

table_insert("↔E", Assumptions, Premisses, (L → R) ∧ (R → L), TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L ↔ R],
	
	P = [   _, I,             L ↔ R,    _, _],
	C = [AIdx, _, (L → R) ∧ (R → L), "↔E", [I]],

	TblIn = [_, Right0],
	
	once((table_append(left, P, Right0, Right1, TblIn, TblB1),
	table_append(left, C, Right1, _, TblB1, TblOut))).

table_insert("→E", Assumptions, Premisses, R, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L, L → R],
	
	LR  = [_, 			I_LR, (L → R), _   , _],
	P_L = [_, 			I_L ,  L     , _   , _],
	P_R = [AIdx,           _,  R 	 , "→E", [I_LR, I_L]],

	TblIn = [_, Right0],

	once((table_append(left, LR, Right0, Right1, TblIn, TblB0),
	table_append(right, P_R, Right1, Right2, TblB0, TblB1),
	table_append(right, P_L, Right2, _, TblB1, TblOut))).

table_insert("∨E", Assumptions, Premisses, C, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L ∨ R, L → C, R → C],

	X =  [_, 				I_LR, L ∨ R,    _, _],
	LC = [_, 				I_L , L → C,    _, _],
	RC = [_, 				I_R , R → C,    _, _],
	Co = [AIdx,    			   _,     C, "∨E", [I_LR, I_L, I_R]],

	TblIn = [_, Right0],

	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, LC, Right2, Right3, TblB1, TblB2),
	table_append(right, RC, Right3, _, TblB2, TblOut))).

table_insert("∨I", Assumptions, Premisses, L ∨ R, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [R],

	P_R = [   _, I_R,     R,    _, _],
	C   = [AIdx,   _, L ∨ R, "∨I", [I_R]],

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(right, P_R, Right1, _, TblB0, TblOut))).

table_insert("∨I", Assumptions, Premisses, L ∨ R, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [L],

	P_R = [   _, I_R,     L,    _, _],
	C   = [AIdx,   _, L ∨ R, "∨I", [I_R]],

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB1),
	table_append(right, P_R, Right1, _, TblB1, TblOut))).

table_insert("¬E", Assumptions, Premisses, C, TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [¬(C), ⊥(N)],

	X =  [   [J], 	   J, ¬(C),  "A", []],
	W =  [	   _, 	 I_W, ⊥(N),    _, _],
	Co = [  AIdx,      _,    C, "¬E", [J, I_W]],

	TblIn = [_, Right0],
	
	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, W, Right2, _, TblB1, TblOut))).

table_insert("¬I", Assumptions, Premisses, ¬(C), TblIn, TblOut) :-
	assumption_index(Assumptions, AIdx, TblIn),
	Premisses = [C, ⊥(N)],

	X =  [[J]  ,   J,    C,  "A", []],
	W =  [    _, I_W, ⊥(N),    _, _],
	Co = [AIdx ,   _, ¬(C), "¬I", [J, I_W]],

	TblIn = [_, Right0],

	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, W, Right2, _, TblB1, TblOut))).


% defines all the indices of Tbl, starting with index I.
idx_define(_, []) :- !.
idx_define(I, Tbl) :-
	J is I + 1,
	Tbl = [First | Last],
	First = [_, I, _, _, _],
	idx_define(J, Last).

idx_define(Tbl) :-
	idx_define(1, Tbl).

% Defines all the indices of the 
% right elements (derivations from conclusion) of Tbl1
% which occur in Tb1 but not in Tbl0  
complete_subproof(Tbl0, Tbl1, TblOut) :-
	Tbl0 = [    _, Right0],
	Tbl1 = [Left1, Right1],
	append(Left2, Right0, Right1),
	append(Left1, Left2, Left),
	idx_define(Left),
	TblOut = [Left, Right0].


% defines the last index and finishes the table.
define_table(TblIn, TblOut) :-
	append(TblIn, TblB),
	idx_define(TblB),
	remove_useless(TblB, TblOut).

table_replace(_, _, [], []) :- !.
table_replace(Old, New, TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	X = [A, I, Old, R, P],
	Y = [A, I, New, R, P],
	table_replace(Old, New, TblNxt, TblNxtOut),
	append([Y], TblNxtOut, TblOut), !.
table_replace(Old, New, TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	table_replace(Old, New, TblNxt, TblNxtOut),
	append([X], TblNxtOut, TblOut).

table_replace_T(_, _, [], []) :- !.
table_replace_T(Old, New, TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	X = Old,
	Y = New,
	table_replace(Old, New, TblNxt, TblNxtOut),
	append([Y], TblNxtOut, TblOut), !.
table_replace_T(Old, New, TblIn, TblOut) :-
	TblIn = [X | TblNxt],
	table_replace(Old, New, TblNxt, TblNxtOut),
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