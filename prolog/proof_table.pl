%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proof_table, [
				   		table_insert/6,
				   		table_init/3,
				   		is_proof_table/1,
				   		write_proof_table/1,
				   		define_table/2,
				   		complete_subproof/2
				   		]).

:-use_module(list_helper).
:-use_module(no_unify).
:-use_module(set).
:-use_module(graph).
:-use_module(proposition).

:- use_module(library(clpfd)).

% Inits the table with his base assumptions and the conclusion.
table_init(Assumptions, Conclusion, Tbl) :-
	findall(X, (A ∈ Assumptions, X = [[A], A, "A", []]), AssumptionTable),
	C = [[_, Conclusion, _, _]],
	Tbl = [AssumptionTable, C].

table_append(_, Element, TblIn, TblIn) :-
	TblIn = [Left, _],
	Element ∈ Left.

table_append(right, Element, TblIn, TblIn) :-
	TblIn = [_, Right],
	Element ∈ Right.

table_append(left, Element, TblIn, TblOut) :-
	TblIn = [Left, Right],
	append(Left, [Element], LeftOut),
	TblOut = [LeftOut, Right].

table_append(right, Element, TblIn, TblOut) :-
	TblIn = [Left, Right],
	append([Element], Right, RightOut),
	TblOut = [Left, RightOut].

table_insert("∧I", Assumptions, Premisses, L ∧ R, TblIn, TblOut) :-
	Premisses = [L, R],

	C   = [Assumptions, L ∧ R, "∧I", [P_L, P_R]],
	P_L = [_          , L    ,  _  , _         ],
	P_R = [_          ,     R,  _  , _         ], 

	table_append(right, C  , TblIn, TblB0 ),
	table_append(right, P_L, TblB0, TblB1 ),
	table_append(right, P_R, TblB1, TblOut).

table_insert("↔I", Assumptions, Premisses, L ↔ R, TblIn, TblOut) :-
	Premisses = [L → R, R → L],

	C   = [Assumptions, L ↔ R, "↔I", [P_L, P_R]],
	P_L = [_          , L → R, _   , _         ],
	P_R = [_          , R → L, _   , _         ], 

	table_append(right, C  , TblIn, TblB0 ),
	table_append(right, P_L, TblB0, TblB1 ),
	table_append(right, P_R, TblB1, TblOut).

table_insert("→I", Assumptions, Premisses, L → R, TblIn, TblOut) :-
	Premisses = [L, R],
	L ∉ Assumptions,

	C   = [Assumptions, L → R, "→I", [X, P_R]],
	X   = [[L]        , L    , "A" ,       []],
	P_R = [_          , R    , _   ,        _],

	table_append(right, C  , TblIn, TblB0 ),
	table_append(left , X  , TblB0, TblB1 ),
	table_append(right, P_R, TblB1, TblOut).

table_insert("∧E", Assumptions, Premisses, L, TblIn, TblOut) :-
	Premisses = [L ∧ R],

	P_LR = [_          , L ∧ R, _   , _     ],
	C    = [Assumptions, L    , "∧E", [P_LR]],
	
	table_append(left, P_LR, TblIn, TblB1 ),
	table_append(left, C   , TblB1, TblOut).

table_insert("∧E", Assumptions, Premisses, R, TblIn, TblOut) :-
	Premisses = [L ∧ R],
	
	P_LR = [_          ,L ∧ R, _   , _     ],
	C =    [Assumptions,    R, "∧E", [P_LR]],
	
	table_append(left, P_LR, TblIn, TblB1 ),
	table_append(left, C   , TblB1, TblOut).

table_insert("↔E", Assumptions, Premisses, (L → R) ∧ (R → L), TblIn, TblOut) :-
	Premisses = [L ↔ R],
	
	P = [_          , L ↔ R            , _   , _  ],
	C = [Assumptions, (L → R) ∧ (R → L), "↔E", [P]],
	
	table_append(left, P, AIdx, TblIn, TblB1 ),
	table_append(left, C, AIdx, TblB1, TblOut).

table_insert("→E", Assumptions, Premisses, R, TblIn, TblOut) :-
	Premisses = [L, L → R],
	
	LR  = [_          , (L → R), _   , _        ],
	P_L = [_          ,  L     , _   , _        ],
	P_R = [Assumptions,      R , "→E", [LR, P_L]],

	table_append(right, P_R, TblIn, TblB0 ),
	table_append(left ,  LR, TblB0, TblB1 ),
	table_append(right, P_L, TblB1, TblOut).

table_insert("∨E", Assumptions, Premisses, C, TblIn, TblOut) :-
	Premisses = [L ∨ R, L → C, R → C],

	X =  [_          , L ∨ R,    _, _          ],
	LC = [_          , L → C,    _, _          ],
	RC = [_          , R → C,    _, _          ],
	Co = [Assumptions,     C, "∨E", [X, LC, RC]],

	table_append(right, Co, TblIn, TblB0 ),
	table_append(left,   X, TblB0, TblB1 ),
	table_append(right, LC, TblB1, TblB2 ),
	table_append(right, RC, TblB2, TblOut).

table_insert("∨I", Assumptions, Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [R],

	P_R = [_          ,     R,    _, _    ],
	C   = [Assumptions, L ∨ R, "∨I", [P_R]],

	table_append(right, C  , TblIn, TblB0 ),
	table_append(right, P_R, TblB0, TblOut).

table_insert("∨I", Assumptions, Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [L],

	P_R = [_,           L    ,    _, _    ],
	C   = [Assumptions, L ∨ R, "∨I", [P_R]],

	table_append(right, C  , TblIn, TblB1 ),
	table_append(right, P_R, TblB1, TblOut).

table_insert("¬E", Assumptions, Premisses, C, TblIn, TblOut) :-
	Premisses = [¬(C), ⊥(N)],
	¬(C) ∉ Assumptions,

	X =  [[¬(C)]      , ¬(C), "A", []     ],
	W =  [_           , ⊥(N), _  ,_       ],
	Co = [Assumptions ,   C , "¬E", [X, W]],
	
    table_append(right, Co, TblIn, TblB0 ),
	table_append(left , X , TblB0, TblB1 ),
	table_append(right, W , TblB1, TblOut).

table_insert("¬I", Assumptions, Premisses, ¬(C), TblIn, TblOut) :-
	Premisses = [C, ⊥(N)],
	C ∉ Assumptions,

	X =  [[C]         , C   , "A" , []    ],
	W =  [_           , ⊥(N), _   , _     ],
	Co = [Assumptions , ¬(C), "¬I", [X, W]],

	table_append(right, Co, TblIn, TblB0),
	table_append(left , X , TblB0, TblB1),
	table_append(right, W , TblB1, TblOut).

not_descriped(Element) :- member(X, Element), var(X).

% Defines all the indices of the 
% right elements (derivations from conclusion) of Tbl1
% which occur in Tb1 but not in Tbl0  
%complete_subproof(Tbl0, Tbl1, TblOut) :-
%	Tbl0 = [    _, Right0],
%	Tbl1 = [Left1, Right1],
%	append(Left2, Right0, Right1),
%	append(Left1, Left2, Left),
%	idx_define(Left),
%	TblOut = [Left, Right0].

complete_subproof(TblIn, TblOut) :-
	TblIn = [Left, Right],
	split_list(Right, L, R, proof_table:not_descriped),
	append(Left, L, LeftOut),
	TblOut = [LeftOut, R].


is_proof_table(Tbl) :-
	findall(X, (X ∈ Tbl,
			    X = [A1, A2, A3, _, A5],
				is_list(A1), is_list(A5),
				is_of_type(positive_integer, A2),
				formula(A3)),
			NewTbl),
	Tbl = NewTbl.

define_table(TblIn, TblOut) :-
	append(TblIn, TblOut).

write_proof_table(Tbl) :-
	is_proof_table(Tbl),
	nl,
	foreach(X ∈ Tbl, write_term(X, [max_depth(0), nl(true)])).



