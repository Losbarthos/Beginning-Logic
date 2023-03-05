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
	findall(X, (nth1(I, Assumptions, A), X = [[I], [I], I, A, "A", []]), AssumptionTable),
	findall(I, ([_, _, I, _, _, _] ∈ AssumptionTable), AIdx),
	C = [[AIdx, _, _, Conclusion, _, _]],
	Tbl = [AssumptionTable, C].

table_append(_, Element, Assumptions, TblIn, TblIn) :-
	TblIn = [Left, _],
	Element = [AIdx, _, _, _, _, _],
	Element ∈ Left,
	(   is_list(Assumptions) ->
        subset(AIdx, Assumptions)
    ;   true
    ).

table_append(_, Element, Assumptions, TblIn, TblIn) :-
	TblIn = [_, Right],
	Element = [AIdx, A, _, _, _, _],
	Element ∈ Right, acyclic_term(A),
	(   is_list(Assumptions) ->
        subset(AIdx, Assumptions)
    ;   true
    ).

table_append(left, Element, AIdx, TblIn, TblOut) :-
	TblIn = [Left, Right],
	Element = [AIdx, A, N, C, R, P],
	length(Left, I), N #= I + 1,
	set_evaluate(A, AA), 
	append(Left, [[AIdx, AA, N, C, R, P]], LeftOut),
	TblOut = [LeftOut, Right].

table_append(right, Element, AIdx, TblIn, TblOut) :-
	Element = [AIdx, AA, I, C, R, P],
	set_evaluate(AA, A), subset(A, AIdx),
	table_append(left, [AIdx, A, I, C, R, P], TblIn, TblOut).

table_append(right, Element, A, TblIn, TblOut) :-
	TblIn = [Left, Right],
	Element = [A, _, I, _, _, _], var(I),
	append([Element], Right, RightOut),
	TblOut = [Left, RightOut].

table_insert("∧I", Premisses, L ∧ R, TblIn, TblOut) :-
	Premisses = [L, R],

	C   = [AIdxC, AC, IC, L ∧ R, "∧I", [IL, IR]],
	P_L = [AIdxL, AL, IL, L    ,  _  , _      ],
	P_R = [AIdxR, AR, IR,     R,  _  , _      ], 

	AC = ((AR) ∪ (AL)), IL #< IC, IR #< IC,

	once((
			table_append(right, C  , AIdxC, TblIn, TblB0 ),
			table_append(right, P_L, AIdxC, TblB0, TblB1 ),
			table_append(right, P_R, AIdxC, TblB1, TblOut),
			(   (var(AIdxL)) ->
		        AIdxL = AIdxC
		    ;   true
		    ),
			(   (var(AIdxR)) ->
		        AIdxR = AIdxC
		    ;   true
		    ),
			(   (nonvar(AIdxR), nonvar(AIdxL)) ->
		        subset(AIdxR, AIdxC), subset(AIdxL, AIdxC)
		    ;   true
		    ))).

table_insert("↔I", Premisses, L ↔ R, TblIn, TblOut) :-
	Premisses = [L → R, R → L],

	C   = [AIdxC, AC, IC, L ↔ R, "↔I", [IL, IR]],
	P_L = [AIdxL, AL, IL, L → R, _   , _       ],
	P_R = [AIdxR, AR, IR, R → L, _   , _       ], 

	AC = ((AR) ∪ (AL)), IL #< IC, IR #< IC,

	once((
			table_append(right, C  , AIdxC, TblIn, TblB0 ),
			table_append(right, P_L, AIdxC, TblB0, TblB1 ),
			table_append(right, P_R, AIdxC, TblB1, TblOut),
			(   (var(AIdxL)) ->
		        AIdxL = AIdxC
		    ;   true
		    ),
			(   (var(AIdxR)) ->
		        AIdxR = AIdxC
		    ;   true
		    ),
			(   (nonvar(AIdxR), nonvar(AIdxL)) ->
		        AIdxC := (AIdxL ∪ AIdxR)
		    ;   true
		    ))).


table_insert("→I", Premisses, L → R, TblIn, TblOut) :-
	Premisses = [L, R],

	C   = [AIdxC, AC  , IC, L → R, "→I", [IA, IR]],
	X   = [[IA] , [IA], IA, L    , "A" ,       []],
	P_R = [AIdxR, AR  , IR,     R, _   ,        _],

	AC = ((AR) \\ ([IA])), IA #< IR, IR #< IC, 

	once((
			table_append(right, C  , AIdxC, TblIn, TblB0 ),
			table_append(left , X  , [IA] , TblB0, TblB1 ),
			table_append(right, P_R, AIdxR, TblB1, TblOut),
			nonvar(AIdxC),
			(   (var(AIdxR)) ->
				union(AIdxC, [IA], AIdxR) 
		    ;   true
		    ))).

table_insert("∧E", Premisses, L, TblIn, TblOut) :-
	Premisses = [L ∧ R],

	P_LR = [AIdx, ALR, ILR, L ∧ R, _   , _    ],
	C    = [AIdx, ALR, IC , L    , "∧E", [ILR]],
	ILR #< IC,

	once((
			table_append(left, P_LR, AIdx, TblIn, TblB1 ),
			table_append(left, C   , AIdx, TblB1, TblOut))).

table_insert("∧E", Premisses, R, TblIn, TblOut) :-
	Premisses = [L ∧ R],
	
	P_LR = [AIdx, ALR, ILR, L ∧ R, _    , _    ],
	C =    [AIdx, ALR, IC ,     R, "∧E" , [ILR]],
	ILR #< IC,
	
	once((
			table_append(left, P_LR, AIdx, TblIn, TblB1 ),
			table_append(left, C   , AIdx, TblB1, TblOut))).

table_insert("↔E", Premisses, (L → R) ∧ (R → L), TblIn, TblOut) :-
	Premisses = [L ↔ R],
	
	P_LR = [AIdx, ALR, ILR,       L ↔ R       , _   , _    ],
	C    = [AIdx, ALR, IC , (L → R) ∧ (R → L) , "↔E", [ILR]],
	ILR #< IC,

	once((
			table_append(left, P_LR, AIdx, TblIn, TblB1 ),
			table_append(left, C   , AIdx, TblB1, TblOut))).

table_insert("→E", Premisses, R, TblIn, TblOut) :-
	Premisses = [L, L → R],

	LR  = [AIdxLR, ALR, ILR, (L → R), _   , _        ],
	P_L = [AIdxL , AL , IL ,  L     , _   , _        ],
	P_R = [AIdxR , AR , IR ,      R , "→E", [IL, ILR]],

	AR = ((ALR) ∪ (AL)), ILR #< IR, IL #< IR,

	once((
			table_append(right, P_R, AIdxR, TblIn, TblB0 ),
			table_append(left ,  LR, AIdxR, TblB0, TblB1 ),
			table_append(right, P_L, AIdxR, TblB1, TblOut),
			(   (var(AIdxL), var(AIdxR)) ->
		        AIdxL = AIdxLR,
		        AIdxR = AIdxLR
		    ;   true
		    ),
			(   (var(AIdxR)) ->
		        AIdxR := (AIdxLR ∪ AIdxL)
		    ;   true
		    ))).
	

table_insert("∨E", Premisses, C, TblIn, TblOut) :-
	Premisses = [L ∨ R, L → C, R → C],

	X =  [_     , AX, IX, L ∨ R,    _, _           ],
	LC = [AIdxLC, AL, IL, L → C,    _, _           ],
	RC = [AIdxRC, AR, IR, R → C,    _, _           ],
	Co = [AIdxC , AC, IC,     C, "∨E", [IX, IL, IR]],

	AC = (((AL) ∪ (AR)) ∪ (AX)), IL #< IC, IR #< IC, IX #< IC,

	once((
			table_append(right, Co, AIdxC, TblIn, TblB0 ),
			table_append(left,   X, AIdxC, TblB0, TblB1 ),
			table_append(right, LC, AIdxC, TblB1, TblB2 ),
			table_append(right, RC, AIdxC, TblB2, TblOut),
			(   (var(AIdxLC)) ->
		        AIdxLC = AIdxC
		    ;   true
		    ),
			(   (var(AIdxRC)) ->
		        AIdxRC = AIdxC
		    ;   true
		    ))).

table_insert("∨I", Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [R],

	P_R = [AIdxR, AC, IR,     R,    _, _   ],
	C   = [AIdxC, AC, IC, L ∨ R, "∨I", [IR]],
	IR #< IC,

	once((
			table_append(right, C  , AIdxC, TblIn, TblB0 ),
			table_append(right, P_R, AIdxC, TblB0, TblOut),
			(   (var(AIdxR)) ->
		        AIdxR = AIdxC
		    ;   true
		    ))).

table_insert("∨I", Premisses, L ∨ R, TblIn, TblOut) :-
	Premisses = [L],

	P_R = [AIdxR, AC, IR, L    ,    _, _   ],
	C   = [AIdxC, AC, IC, L ∨ R, "∨I", [IR]],
	IR #< IC,

	once((
			table_append(right, C  , AIdxC, TblIn, TblB1 ),
			table_append(right, P_R, AIdxC, TblB1, TblOut),
			(   (var(AIdxR)) ->
		        AIdxR = AIdxC
		    ;   true
		    ))).

table_insert("¬E", Premisses, C, TblIn, TblOut) :-
	Premisses = [¬(C), ⊥(N)],

	NA =  [[IA] , [IA], IA, ¬(C), "A" , []      ],
	W  =  [AIdxW, AW  , IW, ⊥(N), _   , _       ],
	A  =  [AIdxC, AC  , IC,   C , "¬E", [IA, IW]],
	
	AC = ((AW) \\ ([IA])), IA #< IC, IW #< IC,

    once((
    		table_append(right, A , AIdxC, TblIn, TblB0 ),
			table_append(left , NA, [IA] , TblB0, TblB1 ),
			table_append(right, W , AIdxW, TblB1, TblOut),
			nonvar(AIdxC),
			(   (var(AIdxW)) ->
				union(AIdxC, [IA], AIdxW) 
		    ;   true
		    ))).


table_insert("¬I", Premisses, ¬(C), TblIn, TblOut) :-
	Premisses = [C, ⊥(N)],

	A  =  [[IA] , [IA], IA, C   , "A" , []      ],
	W  =  [AIdxW, AW  , IW, ⊥(N), _   , _       ],
	NA =  [AIdxC, AC  , IC, ¬(C), "¬I", [IA, IW]],

	AC = ((AW) \\ ([IA])), IA #< IC, IW #< IC, 

	once((
			table_append(right, NA, AIdxC, TblIn, TblB0),
			table_append(left , A , [IA] , TblB0, TblB1),
			table_append(right, W , AIdxW, TblB1, TblOut),
			nonvar(AIdxC),
			(   (var(AIdxW)) ->
				union(AIdxC, [IA], AIdxW) 
		    ;   true
		    ))).

descriped(Element) :- 
	Element = [_, AA, _, _, _, P], 
	set_evaluate(AA, A), nonvar(P), nonvar(A),
	list_without_variables(P), list_without_variables(A).

% and the second element of the Line of ProofTable with I.
add_to_l([_, _, I, _, _, _], I).

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
			  	[_, RG, I, C, R, PP] ∈ TblIn, 
				set_evaluate(RG, AA), sort(AA, A), sort(PP, P),
				X = [A, I, C, R, P]
			  ), 
			TblOut).

define_table(TblIn, TblOut) :-
	complete_subproof(TblIn, TblInU),
	append(TblInU, TblB),
	length(TblB, N),
	last(TblB, [_, _, N, _, _, _]),
	tblfd_to_tbllist(TblB, TblOut).

write_proof_table(Tbl) :-
	is_proof_table(Tbl),
	nl,
	foreach(X ∈ Tbl, write_term(X, [max_depth(0), nl(true)])).



