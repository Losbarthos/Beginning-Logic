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
% checks, if some element is in table
%is_in_table(left, Element, Tbl) :-
%	Tbl = [Left, _],
%	Element ∈ Left.
%is_in_table(right, Element, Tbl) :-
%	Tbl = [_, Right],
%	Element ∈ Right.


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

	C   = [origin([A_C], R_C),     _, L ∧ R, "∧I", [I_L, I_R]],
	P_L = [origin([A_L], R_L), 			             I_L, L    , _   , _         ],
	P_R = [origin([A_R], R_R), 			             I_R, R    , _   , _         ], 

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
	P_R = [origin(A_R, _), I_R, R, _, _],

	TblIn = [_, Right0],

	once((table_append(right, C, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, P_R, Right2, _, TblB1, TblB2),
	member(J, A_R))),
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
	W = [origin(A_W, _), 	 I_W, ⊥(N),    _, _],
	Co = [origin([I_W], [J]),   _,    C, "¬E", [J, I_W]],

	TblIn = [_, Right0],
	
	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, W, Right2, _, TblB1, TblB2),
	member(J, A_W))),
	table_adjust_idx(TblB2, TblOut).

table_insert("¬I", Premisses, ¬(C), TblIn, TblOut) :-
	Premisses = [C, ⊥(N)],

	X =  [origin([J], []),     J,    C,  "A", []],
	W =  [origin(A_W, _),    I_W, ⊥(N),    _, _],
	Co = [origin([I_W], [J]),  _, ¬(C), "¬I", [J, I_W]],

	TblIn = [_, Right0],

	once((table_append(right, Co, Right0, Right1, TblIn, TblB0),
	table_append(left, X, Right1, Right2, TblB0, TblB1),
	table_append(right, W, Right2, _, TblB1, TblB2),
	member(J, A_W))),
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



