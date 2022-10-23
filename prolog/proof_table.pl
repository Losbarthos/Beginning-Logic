%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proof_table, [
				   		table_insert/5,
				   		table_init/3,
				   		table_replace/4,
				   		table_replace_T/4,
				   		is_proof_table/1,
				   		write_proof_table/1,
				   		define_table/2
				   		]).

:-use_module(list_helper).
:-use_module(no_unify).
:-use_module(set).
:-use_module(graph).
:-use_module(proposition).

:- use_module(library(clpfd)).

assumptions([],[],_) :- !.
assumptions(List, Assumptions, Tbl) :-
	List = [V | IRest],
	var(V),
	assumptions(IRest, ARest, Tbl),
	Assumptions = [V | ARest], !.	
assumptions(List, Assumptions, Tbl) :-
	List = [I | IRest],
	Row = [A, I, _, _, _], Row ∈ Tbl,
	A = origin([I],[]),
	assumptions(IRest, ARest, Tbl),
	Assumptions = [I | ARest], !.
assumptions(List, Assumptions, Tbl) :-
	List = [I | I2],
	Row = [origin(I1, E1), I, _, _, _], Row ∈ Tbl,
	union(I1, I2, IRest),
	assumptions(IRest, AssumptionsOR, Tbl),
	subtract(AssumptionsOR, E1, Assumptions).

assumptions(TblIn, TblOut) :-
	findall(X, ([origin(ALIn, ExIn), I, C, R, PL] ∈ TblIn, 
			    assumptions(ALIn, ALOutUS, TblIn),
			    sort(ALOutUS, ALOutNE), 
			    subtract(ALOutNE, ExIn, ALOut),
			    X = [ALOut, I, C, R, PL]), TblOut).

assumptions_origin(TblIn, TblOut) :-
	TblIn = [Left, Right],
	findall(X, ([origin(ALIn, ExIn), I, C, R, PL] ∈ Left, 
				assumptions(ALIn, ALOutUS, Left),
			    X = [origin(ALOutUS, ExIn), I, C, R, PL]), LeftOut),
	TblOut = [LeftOut, Right].


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
get_new_index(right, _, _) :- !.
%	get_last_index(Tbl, N), length_of(right, Tbl, L),
%	N #= I + L.


% Gets some Index of the right Part of the table.
table_idx(left, Tbl, P, Idx) :-
	Tbl = [Left, _],
	Element = [R, A, I, P, _, _],
	Idx = [R, A, I],
	Element ∈ Left.

table_idx(right, Tbl, P, Idx) :-
	Tbl = [_, Right],
	Element = [R, A, I, P, _, _],
	Idx = [R, A, I],
	Element ∈ Right.

crop(X, To, To) :- 
	not(var(X)), 
	X = [], !.
crop(X, From, To) :-
	not(var(X)),
	X = [I | XR],
	is_of_type(integer, I),
	crop(XR, From, To), !.
crop(X, From, To) :-
	not(var(X)),
	X = [I | XR],
	crop(XR, From, To),

	is_member_of([_, I, _, _, _], To), !.
crop(X, From, To) :-
	not(var(X)),
	X = [I | XR],
	crop(XR, From, Between),
	is_nth1(N, Between, [_, I, _, _, _]),
	split_list_at_nth1(N, Between, To, _), !.
crop(_, To, To) :- !.

crop(_, _, [], []) :- !.
crop(X, C, From, To) :-
	last(From, [_, _, C, _, _]),
	crop(X, From, To), !.
crop(X, C, From, To) :-
	without_last(From, Between),
	crop(X, C, Between, To), !.

table_append(left, Element, PRight, PRight, TblIn, TblOut) :-
	TblIn = [Left, _],
	Element ∈ Left,
	assumptions_origin(TblIn, TblOut).

table_append(left, Element, PRight, PRight, TblIn, TblOut) :-
	Element ∈ PRight,
	assumptions_origin(TblIn, TblOut).

table_append(left, Element, PRight, PRight, TblIn, TblOut) :-
	TblIn = [Left, Right],
	get_new_index(left, TblIn, I),
	Element = [_, I, _, _, _],
	append(Left, [Element], LeftOut),
	TblOutB = [LeftOut, Right],
	assumptions_origin(TblOutB, TblOut).

table_append(right, Element, PRight, PRight, TblIn, TblOut) :-
	TblIn = [Left, _],
	Element ∈ Left,
	assumptions_origin(TblIn, TblOut).

table_append(right, Element, PRight, NewRight, TblIn, TblOut) :-
	Element = [_, I, C, _, X],
	crop(X, C, PRight, NewRight),
	Element ∈ NewRight, var(I),
	assumptions_origin(TblIn, TblOut).

table_append(right, Element, PRight, NewRight, TblIn, TblOut) :-
	TblIn = [Left, Right],
	get_new_index(right, TblIn, I),
	Element = [_, I, _, _, _],
	append([Element], Right, RightOut),
	append([Element], PRight, NewRight),
	TblOutB = [Left, RightOut], var(I),
	assumptions_origin(TblOutB, TblOut).

% defines the last index and finishes the table.
define_table(TblIn, TblOut) :-
	TblIn = [TblB, _],
	assumptions(TblB, TblOut).

table_init(Assumptions, Conclusion, Tbl) :-
	findall(X, (nth1(N, Assumptions, A), X = [origin([N], []), N, A, "A", []]), AssumptionTable),
	C = [[_, _, Conclusion, _, _]],
	Tbl = [AssumptionTable, C].

get_first_solved([], _) :- false, !.
get_first_solved(List, First) :-
	List = [First | _],
	First = [origin(A, RM), _, _, R, P],
	integer_list(A),
	integer_list(RM),
	string(R),
	integer_list(P), !.
get_first_solved(List, First) :-
	List = [_ | ListNext],
	get_first_solved(ListNext, First), !.

append_first_solved(First, Left, LeftNew) :-
	First = [_, M, _, _, _],
	length(Left, N),
	M is N + 1,
	append(Left, [First], LeftNew).

table_adjust_idx(TblIn, TblOut) :-
	TblIn = [Left, Right],
	get_first_solved(Right, First),
	delete(Right, First, RightNew),
	append_first_solved(First, Left, LeftNew),
	TblB = [LeftNew, RightNew], 
	table_adjust_idx(TblB, TblOut),
	!.
table_adjust_idx(Tbl, Tbl).

table_insert("∧I", Premisses, L ∧ R, TblIn, TblOut) :-
	Premisses = [L, R],

	C   = [origin([I_L, I_R], []),     _, L ∧ R, "∧I", [I_L, I_R]],
	P_L = [_, 			             I_L, L    , _   , _         ],
	P_R = [_, 			             I_R, R    , _   , _         ], 

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(right, P_L, Right1, Right2, TblB0, TblB1),
	table_append(right, P_R, Right2, _, TblB1, TblB2))),
	table_adjust_idx(TblB2, TblOut).

table_insert("↔I", Premisses, L ↔ R, TblIn, TblOut) :-
	Premisses = [L → R, R → L],

	C   = [origin([I_L, I_R], []),     _, L ↔ R, "↔I", [I_L, I_R]],
	P_L = [_, 			             I_L, L → R, _   , _         ],
	P_R = [_, 			             I_R, R → L, _   , _         ], 

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(right, P_L, Right1, Right2, TblB0, TblB1),
	table_append(right, P_R, Right2, _, TblB1, TblB2))),
	table_adjust_idx(TblB2, TblOut).

table_insert("→I", Premisses, L → R, TblIn, TblOut) :-
	Premisses = [L, R],

	C = [origin([I_R], [J]), _, L → R, "→I", [J, I_R]],
	X = [origin([J],[]), J, L, "A", []],
	P_R = [_, I_R, R, _, _],

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, P_R, Right2, _, TblB1, TblB2))),
	%member(J, A_R))),
	table_adjust_idx(TblB2, TblOut).

table_insert("∧E", Premisses, L, TblIn, TblOut) :-
	Premisses = [L ∧ R],

	P_LR = [_, I, L ∧ R, _, _],
	C = [origin([I], []), _, L, "∧E", [I]],

	TblIn = [_, Right0],
	
	once((table_append(left, P_LR, Right0, Right1, TblIn, TblB1),
	table_append(left, C, Right1, _, TblB1, TblB2))),
	table_adjust_idx(TblB2, TblOut).

table_insert("∧E", Premisses, R, TblIn, TblOut) :-
	Premisses = [L ∧ R],
	
	P_LR = [_, I, L ∧ R, _, _],
	C = [origin([I], []), _, R, "∧E", [I]],

	TblIn = [_, Right0],
	
	once((table_append(left, P_LR, Right0, Right1, TblIn, TblB1),
	table_append(left, C, Right1, _, TblB1, TblB2))),
	table_adjust_idx(TblB2, TblOut).

table_insert("↔E", Premisses, (L → R) ∧ (R → L), TblIn, TblOut) :-
	Premisses = [L ↔ R],
	
	P = [_, I, L ↔ R, _, _],
	C = [origin([I], []), _, (L → R) ∧ (R → L), "↔E", [I]],

	TblIn = [_, Right0],
	
	once((table_append(left, P, Right0, Right1, TblIn, TblB1),
	table_append(left, C, Right1, _, TblB1, TblB2))),
	table_adjust_idx(TblB2, TblOut).

table_insert("→E", Premisses, R, TblIn, TblOut) :-
	Premisses = [L, L → R],
	
	LR  = [_, 			I_LR, (L → R), _   , _],
	P_L = [_, 			I_L ,  L     , _   , _],
	P_R = [origin([I_LR, I_L], []),    _,  R 	 , "→E", [I_LR, I_L]],

	TblIn = [_, Right0],

	once((table_append(left, LR, Right0, Right1, TblIn, TblB0),
	table_append(right, P_R, Right1, Right2, TblB0, TblB1),
	table_append(right, P_L, Right2, _, TblB1, TblB2))),
	table_adjust_idx(TblB2, TblOut).

table_insert("∨E", Premisses, C, TblIn, TblOut) :-
	Premisses = [L ∨ R, L → C, R → C],

	X =  [_, 				I_LR, L ∨ R,    _, _],
	LC = [_, 				I_L , L → C,    _, _],
	RC = [_, 				I_R , R → C,    _, _],
	Co = [origin([I_LR, I_L, I_R], []),    _,     C, "∨E", [I_LR, I_L, I_R]],

	TblIn = [_, Right0],

	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, LC, Right2, Right3, TblB1, TblB2),
	table_append(right, RC, Right3, _, TblB2, TblB3))),
	table_adjust_idx(TblB3, TblOut).

table_insert("∨I", Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [R],

	P_R = [_, 	I_R,     R,    _, _],
	C = [origin([I_R], []), _  , L ∨ R, "∨I", [I_R]],

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(right, P_R, Right1, _, TblB0, TblB1))),
	table_adjust_idx(TblB1, TblOut).
	

table_insert("∨I", Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [L],

	P_R = [_, I_R, L, 		 _, _],
	C = [origin([I_R], []), _, L ∨ R, "∨I", [I_R]],

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB1),
	table_append(right, P_R, Right1, _, TblB1, TblB2))),
	table_adjust_idx(TblB2, TblOut).
	


table_insert("¬E", Premisses, C, TblIn, TblOut) :-
	Premisses = [¬(C), ⊥(N)],

	X = [origin([J], []), 	   J, ¬(C),  "A", []],
	W = [_, 	 			 I_W, ⊥(N),    _, _],
	Co = [origin([I_W], [J]),  _,    C, "¬E", [J, I_W]],

	TblIn = [_, Right0],
	
	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, W, Right2, _, TblB1, TblB2))),
	%member(J, A_W))),
	table_adjust_idx(TblB2, TblOut).

table_insert("¬I", Premisses, ¬(C), TblIn, TblOut) :-
	Premisses = [C, ⊥(N)],

	X =  [origin([J], []),     J,    C,  "A", []],
	W =  [_,    			 I_W, ⊥(N),    _, _],
	Co = [origin([I_W], [J]),  _, ¬(C), "¬I", [J, I_W]],

	TblIn = [_, Right0],

	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, W, Right2, _, TblB1, TblB2))),
	%member(J, A_W))),
	table_adjust_idx(TblB2, TblOut).

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