%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proof_table, [
				   		table_insert/5,
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
	findall(X, (nth1(I, Assumptions, A), X = [[I], I, A, "A", []]), AssumptionTable),
	C = [[_, _, Conclusion, _, _]],
	Tbl = [AssumptionTable, C].

table_append(_, Element, TblIn, TblIn) :-
	TblIn = [Left, _],
	Element ∈ Left.

table_append(_, Element, TblIn, TblIn) :-
	TblIn = [_, Right],
	Element ∈ Right, 
	Element = [A | _], acyclic_term(A).

table_append(left, Element, TblIn, TblOut) :-
	TblIn = [Left, Right],
	Element = [_, N, _, _, _],
	length(Left, I), N #= I + 1,
	append(Left, [Element], LeftOut),
	TblOut = [LeftOut, Right].

table_append(right, Element, TblIn, TblOut) :-
	Element = [AA, I, C, R, P],
	set_evaluate(AA, A),
	table_append(left, [A, I, C, R, P], TblIn, TblOut).

table_append(right, Element, TblIn, TblOut) :-
	TblIn = [Left, Right],
	Element = [_, I, _, _, _], var(I),
	append([Element], Right, RightOut),
	TblOut = [Left, RightOut].

table_insert("∧I", Premisses, L ∧ R, TblIn, TblOut) :-
	Premisses = [L, R],

	C   = [AC, IC, L ∧ R, "∧I", [IL, IR]],
	P_L = [AL, IL, L    ,  _  , _      ],
	P_R = [AR, IR,     R,  _  , _      ], 

	AC = ((AR) ∪ (AL)), IL #< IC, IR #< IC,

	once((table_append(right, C  , TblIn, TblB0 ),
	table_append(right, P_L, TblB0, TblB1 ),
	table_append(right, P_R, TblB1, TblOut))).

table_insert("↔I", Premisses, L ↔ R, TblIn, TblOut) :-
	Premisses = [L → R, R → L],

	C   = [AC, IC, L ↔ R, "↔I", [IL, IR]],
	P_L = [AL, IL, L → R, _   , _       ],
	P_R = [AR, IR, R → L, _   , _       ], 

	AC = ((AR) ∪ (AL)), IL #< IC, IR #< IC,

	once((table_append(right, C  , TblIn, TblB0 ),
	table_append(right, P_L, TblB0, TblB1 ),
	table_append(right, P_R, TblB1, TblOut))).

table_insert("→I", Premisses, L → R, TblIn, TblOut) :-
	Premisses = [L, R],

	C   = [AC  , IC, L → R, "→I", [IA, IR]],
	X   = [[IA], IA, L    , "A" ,       []],
	P_R = [AR  , IR,     R, _   ,        _],

	AC = ((AR) \\ ([IA])), IA #< IC, IR #< IC,

	once((table_append(right, C  , TblIn, TblB0 ),
	table_append(left , X  , TblB0, TblB1 ),
	table_append(right, P_R, TblB1, TblOut))).

table_insert("∧E", Premisses, L, TblIn, TblOut) :-
	Premisses = [L ∧ R],

	P_LR = [ALR, ILR, L ∧ R, _   , _    ],
	C    = [ALR, IC , L    , "∧E", [ILR]],
	ILR #< IC,

	once((table_append(left, P_LR, TblIn, TblB1 ),
	table_append(left, C   , TblB1, TblOut))).

table_insert("∧E", Premisses, R, TblIn, TblOut) :-
	Premisses = [L ∧ R],
	
	P_LR = [ALR, ILR, L ∧ R, _    , _    ],
	C =    [ALR, IC ,     R, "∧E" , [ILR]],
	ILR #< IC,
	
	once((table_append(left, P_LR, TblIn, TblB1 ),
	table_append(left, C   , TblB1, TblOut))).

table_insert("↔E", Premisses, (L → R) ∧ (R → L), TblIn, TblOut) :-
	Premisses = [L ↔ R],
	
	P_LR = [ALR, ILR,       L ↔ R       , _   , _  ],
	C    = [ALR, IC , (L → R) ∧ (R → L) , "↔E", [ILR]],
	ILR #< IC,

	once((table_append(left, P_LR, TblIn, TblB1 ),
	table_append(left, C, TblB1, TblOut))).

table_insert("→E", Premisses, R, TblIn, TblOut) :-
	Premisses = [L, L → R],

	LR  = [ALR, ILR, (L → R), _   , _        ],
	P_L = [AL , IL ,  L     , _   , _        ],
	P_R = [AR , IR ,      R , "→E", [IL, ILR]],

	AR = ((ALR) ∪ (AL)), ILR #< IR, IL #< IR,

	once((table_append(right, P_R, TblIn, TblB0 ),
	table_append(left ,  LR, TblB0, TblB1 ),
	table_append(right, P_L, TblB1, TblOut))).
	

table_insert("∨E", Premisses, C, TblIn, TblOut) :-
	Premisses = [L ∨ R, L → C, R → C],

	X =  [AX, IX, L ∨ R,    _, _           ],
	LC = [AL, IL, L → C,    _, _           ],
	RC = [AR, IR, R → C,    _, _           ],
	Co = [AC, IC,     C, "∨E", [IX, IL, IR]],

	AC = (((AL) ∪ (AR)) ∪ (AX)), IL #< IC, IR #< IC, IX #< IC,

	once((table_append(right, Co, TblIn, TblB0 ),
	table_append(left,   X, TblB0, TblB1 ),
	table_append(right, LC, TblB1, TblB2 ),
	table_append(right, RC, TblB2, TblOut))).

table_insert("∨I", Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [R],

	P_R = [AC, IR,     R,    _, _   ],
	C   = [AC, IC, L ∨ R, "∨I", [IR]],
	IR #< IC,

	once((table_append(right, C  , TblIn, TblB0 ),
	table_append(right, P_R, TblB0, TblOut))).

table_insert("∨I", Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [L],

	P_R = [AC, IR, L    ,    _, _   ],
	C   = [AC, IC, L ∨ R, "∨I", [IR]],
	IR #< IC,

	once((table_append(right, C  , TblIn, TblB1 ),
	table_append(right, P_R, TblB1, TblOut))).

table_insert("¬E", Premisses, C, TblIn, TblOut) :-
	Premisses = [¬(C), ⊥(N)],

	NA =  [[IA], IA, ¬(C), "A" , []      ],
	W  =  [AW  , IW, ⊥(N), _   , _       ],
	A  =  [AC  , IC,   C , "¬E", [IA, IW]],
	
	AC = ((AW) \\ ([IA])), IA #< IC, IW #< IC,

    once((table_append(right, A, TblIn, TblB0 ),
	table_append(left , NA , TblB0, TblB1 ),
	table_append(right, W , TblB1, TblOut))).


table_insert("¬I", Premisses, ¬(C), TblIn, TblOut) :-
	Premisses = [C, ⊥(N)],

	A  =  [[IA], IA, C   , "A" , []      ],
	W  =  [AW  , IW, ⊥(N), _   , _       ],
	NA =  [AC  , IC, ¬(C), "¬I", [IA, IW]],

	AC = ((AW) \\ ([IA])), IA #< IC, IW #< IC,

	once((table_append(right, NA, TblIn, TblB0),
	table_append(left , A , TblB0, TblB1),
	table_append(right, W , TblB1, TblOut))).

descriped(Element) :- 
	Element = [AA, _, _, _, P], 
	set_evaluate(AA, A), nonvar(P), nonvar(A),
	list_without_variables(P), list_without_variables(A).

% and the second element of the Line of ProofTable with I.
add_to_l([_, I, _, _, _], I).

% Definition of the main function for update all fully descriped values in the table.
update_table([L, R], [L2, R2]) :-
    partition(descriped, R, ToL, R2), % Partition R into the two lists ToL and ToR
    append(L, ToL, L2), % Append ToL to L to form L2
    length(L, N0), N1 #= N0 + 1, length(L2, N2), range(Rg, N1, N2),
    maplist(add_to_l, ToL, Rg), % Update the I values of the appended elements
    !. % The cut ensures that the function only returns one solution

complete_subproof(T, T) :- 
	update_table(T, T), !.
complete_subproof(TBIn, TBOut) :- 
	update_table(TBIn, TBB), complete_subproof(TBB, TBOut).

is_proof_table(Tbl) :-
	findall(X, (X ∈ Tbl,
			    X = [A1, A2, A3, _, A5],
				is_list(A1), is_list(A5),
				is_of_type(positive_integer, A2),
				formula(A3)),
			NewTbl),
	Tbl = NewTbl.


tblfd_to_tbllist(TblIn, TblOut) :-
	findall(X, 
			  (
			  	[RG, I, C, R, PP] ∈ TblIn, 
				set_evaluate(RG, AA), sort(AA, A), sort(PP, P),
				X = [A, I, C, R, P]
			  ), 
			TblOut).

define_table(TblIn, TblOut) :-
	complete_subproof(TblIn, TblInU),
	append(TblInU, TblB),
	length(TblB, N),
	last(TblB, [_, N, _, _, _]),
	tblfd_to_tbllist(TblB, TblOut).

write_proof_table(Tbl) :-
	is_proof_table(Tbl),
	nl,
	foreach(X ∈ Tbl, write_term(X, [max_depth(0), nl(true)])).



