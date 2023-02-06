%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze


:- set_prolog_flag(optimise_unify, false).

:-use_module(list_helper).
:-use_module(set).
:-use_module(invariant).
:-use_module(proposition).
:-use_module(derivation).

:-use_module(graph).
:-use_module(graph_proof).


:-use_module(proof_table).
:-use_module(systeml).

:-use_module(library(http/json)).


% Prints dictionary varlues in a way, every value is on a seperate line in the terminal.
% more details see: https://stackoverflow.com/questions/72238440/swi-prolog-looking-for-a-way-to-print-dictionary-values-in-seperate-lines/72267095?noredirect=1#comment127695212_72267095
portray(Term) :-
    is_dict(Term),
    dict_pairs(Term, Tag, Pairs),
    writef("%p{\n", [Tag]),
    foreach(member(Key-Value, Pairs), writef("\t%p: %p\n\n", [Key, Value])),
    write("}").
portray(Term) :-
	is_proof_table(Term),
	write_proof_table(Term), !.
portray(Term) :-
	is_list(Term),
	write_term(Term, [max_depth(0)]).


%
% Derivations which can used in the proof.
%

% Same as
% A;P?L∧R → A;P?L and A;P?R
% RuleName: ∧I
rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A, P) ⊢ (L ∧ R)), 
	P1 := P ∪ [L],
	NextStep = (((A, P) ⊢ L) ∧ ((A, P1) ⊢ R)),

	
	U := A ∪ P, 
	not(has_contradictions(U)),
	merge_rule_graph([L, R], L ∧ R, "∧I", GIn, GOut),
	
	temp_invariant(A, AT),
	table_insert("∧I", AT, [L, R], L ∧ R, TIn, TOut).

% Same as
% A;P?L↔R → A;P?L→R and A;P?R→L   
% RuleName: ↔I
rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A, P) ⊢ (L ↔ R)), P1 := P ∪ [L → R],% temp(L ↔ R)],
	NextStep = (((A, P) ⊢ (L → R)) ∧ ((A, P1) ⊢ (R → L))),
	
	U := A ∪ P,
	not(has_contradictions(U)),
	merge_rule_graph([L → R, R → L], L ↔ R, "↔I", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("↔I", AT, [L → R, R → L], L ↔ R, TIn, TOut).

% Same as
% [A;P?L→R] L ∈ (A ∪ P) → A;P?R   
%    with
% RuleName: →I
%rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
%	Origin = ((A, P) ⊢ (L → R)), 
%	U:= A ∪ P, L ∈ U, %Pn := P %∪ [temp(L → R)],
%	NextStep = ((A, P) ⊢ R), 
%
%	not(has_contradictions(U)),
%	merge_rule_graph([L, R], L → R, "→I", GIn, GOut),
%	table_insert("→I", [L, R], L → R, TIn, TOut).

% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), L ∉ (A ∪ P)] → A;P,L?C   
%    with
% RuleName: ∧E
rule(Origin, NextStep, GIn, GOut, TIn, TOut) :- 
	Origin = ((A, P1) ⊢ C), NextStep0 = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(L ∉ U), P2 := P1 ∪ [L], 

	((R ∈ U) -> replace_derivation_by_inv(L ∧ R, NextStep0, NextStep);NextStep = NextStep0),

	not(has_contradictions(U)),
	merge_rule_graph([L ∧ R], L, "∧E", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("∧E", AT, [L ∧ R], L, TIn, TOut).




% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;P,R?C   
%    with
% RuleName: ∧E
rule(Origin, NextStep, GIn, GOut, TIn, TOut) :- 
	Origin = ((A, P1) ⊢ C), NextStep0 = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(R ∉ U), P2 := P1 ∪ [R], 
	
	((L ∈ U) -> replace_derivation_by_inv(L ∧ R, NextStep0, NextStep);NextStep = NextStep0),

	not(has_contradictions(U)),

	merge_rule_graph([L ∧ R], R, "∧E", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("∧E", AT, [L ∧ R], R, TIn, TOut).


% Same as
% [A;P?C, (L ↔ R) ∈ (A ∪ P), (L → R) ∧ (R → L) ∉ (A ∪ P)] → A;P,(L → R) ∧ (R → L)?C   
%    with
% RuleName: ↔E
rule(Origin, NextStep, GIn, GOut, TIn, TOut) :- 
	Origin = ((A, P1) ⊢ C), NextStep0 = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ↔ R) ∈ U),
	(((L → R) ∧ (R → L)) ∉ U), P2 := P1 ∪ [(L → R) ∧ (R → L)],

	replace_derivation_by_inv(L ↔ R, NextStep0, NextStep),

	not(has_contradictions(U)),
	merge_rule_graph([L ↔ R], (L → R) ∧ (R → L), "↔E", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("↔E", AT, [L ↔ R], (L → R) ∧ (R → L), TIn, TOut).


%
% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L    
% RuleName: →E
rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A1, P1) ⊢ C), 
	Origin0 = ((A2, P2) ⊢ C), 
	NextStep = (((A2, P2) ⊢ L) ∧ ((A1, P3) ⊢ C)),
	GIn = graph(_, E),
	

	U1 := (A1 ∪ P1), temp_invariant(U1, UT),

	((L → R) ∈ U1), R ∉ UT, not(C=L), 
	P3 := P1 ∪ [L, R], 

	replace_derivation_by_inv(L → R, Origin, Origin0),


	not(((¬(¬(L)) ∈ UT), (edge(¬(¬(L)), ¬(L), "¬E") ∈ E))), % To eliminate derivations like d ⊢ ¬(¬d)
	not(( L = ¬(¬(L1)), (edge(¬(¬(L1)), ¬(L1), "¬I") ∈ E))),% To eliminate derivations like ¬(¬d) ⊢ d

	not(has_contradictions(UT)),
	merge_rule_graph([L, L → R], R, "→E", GIn, GOut),

	temp_invariant(A1, AT),
	table_insert("→E", AT, [L, L → R], R, TIn, TOut).


%
% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P)] → A\(L ∨ R),P\(L ∨ R)?((L → C) ∧ (R → C))    
% RuleName: ∨E
rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A1, P1) ⊢ C), 
	Origin0 = ((A2, P2) ⊢ C), 
	NextStep = (((A2, P2) ⊢ (L → C)) ∧ ((A2, P2) ⊢ (R → C))),
	
	U1 := (A1 ∪ P1), ((L ∨ R) ∈ U1), %subtract(A1, [L ∨ R], A2), subtract(P1, [L ∨ R], P2),

	replace_derivation_by_inv(L ∨ R, Origin, Origin0),

	not(has_contradictions(U1)),

	merge_rule_graph([L ∨ R, L → C, R → C], C, "∨E", GIn, GOut),

	temp_invariant(A1, AT),
	table_insert("∨E", AT, [L ∨ R, L → C, R → C], C, TIn, TOut).



% Same as
% [A;P?L→R] → A,L;P?R   
%    with
% RuleName: →I
c_rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A1, P) ⊢ (L → R)),
	U:= A1 ∪ P, L ∉ U, A2 := A1 ∪ [L], %Pn := P ∪ [temp(L → R)],%, [A1, P]], 
	NextStep = ((A2, P) ⊢ R),

	not(has_contradictions(U)),
	merge_rule_graph([L, R], L → R, "→I", GIn, GOut),

	temp_invariant(A1, AT),
	table_insert("→I", AT, [L, R], L → R, TIn, TOut).



% Same as
% [A;P?L∨R,] → [A;P?L]   
%    with
% RuleName: ∨I
c_rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ L), 
	U:= A ∪ P, 

	not(has_contradictions(U)),
	merge_rule_graph([L], L ∨ R, "∨I", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("∨I", AT, [L], L ∨ R, TIn, TOut).

% Same as
% [A;P?L∨R] → [A;P?R]   
%    with
% RuleName: ∨I
c_rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ R), 
	U:= A ∪ P, 

	not(has_contradictions(U)),
	merge_rule_graph([R], L ∨ R, "∨I", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("∨I", AT, [R], L ∨ R, TIn, TOut).




% Same as
% [A;P?C, (C ∧ ¬C) ∉ A, ¬C ∉ A] → (A,¬C;P?(X1 ∧ ¬X1)) ∨ (A,¬C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,¬C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬E 
% Remark: maybe its better to say ¬Xi ∈ (A ∪ P ∪ {¬C}), but already no counterexample for ¬Xi ∈ (A ∪ P) found.
c_rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A, P) ⊢ C), GIn = graph(V, _),
	not(is_contradiction(C)), U:= A ∪ P, (¬(C) ∉ U), (temp(¬(C)) ∉ U), A0 := A ∪ [¬(C)], 
	once((⊥(N), (⊥(N) ∉ V))),
	NextStep = ((A0, P) ⊢ ⊥(N)),

	merge_rule_graph([¬(C), ⊥(N)], C, "¬E", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("¬E", AT, [¬(C), ⊥(N)], C, TIn, TOut).


% Same as
% [A;P?¬C, (C ∧ ¬C) ∉ A, C ∉ A] → (A,C;P?(X1 ∧ ¬X1)) ∨ (A,C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬I 
c_rule(Origin, NextStep, GIn, GOut, TIn, TOut) :-
	Origin = ((A, P) ⊢ ¬(C)), GIn = graph(V, _),
	not(is_contradiction(C)), U:= A ∪ P, (C ∉ U), (temp(C) ∉ U), A0 := A ∪ [C],
	once((⊥(N), (⊥(N) ∉ V))),
	NextStep = ((A0, P) ⊢ ⊥(N)),

	merge_rule_graph([C, ⊥(N)], ¬(C), "¬I", GIn, GOut),

	temp_invariant(A, AT),
	table_insert("¬I", AT, [C, ⊥(N)], ¬(C), TIn, TOut).


%
% Proofs some Derivation
%

% Preconditions

proof(Derivation, G, G, T, T) :- 	
		isvalid(Derivation),
		!.
proof(Derivation, GIn, G, TIn, T) :- 	
		Derivation = ((A, _) ⊢ ⊥(N)),
		%T = [LeftIn, RightIn],
		%TOut = [LeftOut, RightOut],
		iscontradiction(Derivation, C),
		subs(⊥(N), (C ∧ ¬(C)), TIn, TOut),
		%subs(⊥(N), (C ∧ ¬(C)), RightIn, RightOut),
		replace_vertex_weighted(⊥(N), (C ∧ ¬(C)), GIn, GOut),
		merge_rule_graph([C, ¬(C)], (C ∧ ¬(C)), "∧I", GOut, G),
		table_insert("∧I", A, [C, ¬(C)], (C ∧ ¬(C)), TOut, T),
		!.
proof(Derivation, GIn, G, TIn, T) :- 
		Derivation = ((A, P) ⊢ C),
		U := (A ∪ P),
		not(has_cases(U, C)),
		rule(Derivation, NextStep, GIn, GOut, TIn, TOut),
		proof(NextStep, GOut, G, TOut, T),!.

proof(Derivation, GIn, G, TIn, T) :- 
		c_rule(Derivation, NextStep, GIn, GOut, TIn, TOut), 
		proof(NextStep, GOut, G, TOut, T),!.

proof(Derivation, GIn, G, TIn, T) 	:- 	
		Derivation = (D1 ∧ D2),
		D1 = ((_, _) ⊢ _),
		D2 = ((_, _) ⊢ _),

		proof(D1, GIn, GOut, TIn, TB), complete_subproof(TB, TOut),
		proof(D2, GOut, G, TOut, T).

proof(Derivation, Graph, Table) :- 
	Derivation = (A ⊢ C),
	table_init(A, C, TInit),
	proof(((A, []) ⊢ C), graph([],[]), Graph0, TInit, Table0),
	define_table(Table0, Table1),
	convert_to_systeml(Table1, Table),
	remove_not_sufficcient_vertices(C, Graph0, Graph).


% Examples
% ?- proof((([¬(q),p→q], []) ⊢ ¬(p)), P).
% ?- proof(([p],[]) ⊢ ( (¬(q→r)→ ¬(p)) → (¬(r)→ ¬(q))), P).
%


proof_py(Derivation, GProof, TProof) :-
	proof(Derivation, GProofO, TProofO), 
	term_to_atom(GProofO, GProof),
	term_to_atom(TProofO, TProof), !.
proof_py(Derivation, GProof, TProof) :-
	proof(Derivation, GProofO, _),
	term_to_atom(GProofO, GProof),
	TProof = [].


proof_t(Derivation, Proof) :-
	proof(Derivation, Proof1),
	Proof = Proof1._.

proofD(Derivation, Graph, Table) :-
	format('To prove: ~w~n', [Derivation]),
	proof(Derivation, Graph, Table).

go_proof1(G, T) :- proofD(([p→q,p] ⊢ q), G, T).
go_proof2(G, T) :- proofD(([(¬q),((¬q)→((¬p)→q))] ⊢ ((¬p)→q)), G, T).
go_proof3(G, T) :- proofD(([p→q,q→r,p] ⊢ r), G, T).
go_proof4(G, T) :- proofD(([p→(q→r),p→q,p] ⊢ r), G, T).
go_proof5(G, T) :- proofD(([¬(q),p→q] ⊢ ¬(p)), G, T).
go_proof6(G, T) :- proofD(([p→(q→r),p,¬(r)] ⊢ ¬(q)), G, T).
go_proof8(G, T) :- proofD(([¬(p)→q,¬(q)] ⊢ p), G, T).
go_proof10(G, T) :- proofD(([p→(q→r)] ⊢ (q→(p→r))), G, T).
go_proof11(G, T) :- proofD(([q→r] ⊢ ((¬(q)→ ¬(p))→ (p→r))), G, T).
go_proof12(G, T) :- proofD(([p→ ¬(q), q] ⊢ ¬(p)), G, T).	

go_proof13(G, T) :- proofD(([(p ∧ q) → r] ⊢ (p → (q → r)) ), G, T).
go_proof13_2(G,T) :- proofD(([q → (p → r), ¬(r), q] ⊢ ¬(p)), G, T).

go_proof14(G, T) :- proofD(([p → ¬(¬(q)), p] ⊢ q), G, T).

go_proof25(G, T) :- proofD(([p] ⊢ ((¬(q→r)→ ¬(p))→ (¬(r)→ ¬(q)))), G, T).
go_proof31(G, T) :- proofD(([q → r] ⊢ ((p ∧ q) → (p ∧ r))), G, T).
go_proof32(G, T) :- proofD(([(p ∧ q)] ⊢ (q ∧ p)), G, T).
go_proof33(G, T) :- proofD(([(p∨q)] ⊢ (q∨p)), G, T).
go_proof34(G, T) :- proofD(([(q→r)] ⊢ ((p∨q)→(p∨r))), G, T).
go_proof35(G, T) :- proofD(([(p∨(q∨r))] ⊢ (q∨(p∨r))), G, T).
go_proof41(G, T) :- proofD(([(p∧q)] ⊢ (p∨q)), G, T).
go_proof42(G, T) :- proofD(([(p→r)∧(q→r)] ⊢ ((p∨q)→r)), G, T).
go_proof46(G, T) :- proofD(([p→(q∧r)] ⊢ ((p→q)∧(p→r))), G, T).
go_proof48(G, T) :- proofD(([(p↔q)] ⊢ (q↔p)), G, T).
go_proof50(G, T) :- proofD(([(p↔q),(q↔r)] ⊢ (p↔r)), G, T).

go_debug :-
    set_prolog_flag(color_term, false),
    protocol('p.txt'),
    leash(-all),
    trace(proof/6),
    proof(([(p↔q), (q↔r)],[]) ⊢ (p↔r), _P),
    !,
    nodebug,
    noprotocol.
go_debug :-
    nodebug,
    noprotocol.