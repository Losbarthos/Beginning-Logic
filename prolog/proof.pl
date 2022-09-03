%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze


:- set_prolog_flag(optimise_unify, false).

:-use_module(extend_list).
:-use_module(set).
:-use_module(invariant).
:-use_module(proposition).
:-use_module(derivation).

:-use_module(graph).
:-use_module(graph_proof).


:-use_module(proof_table).

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
rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A, P) ⊢ (L ∧ R)), %not(var(L)), not(var(R)), 
	P1 := P ∪ [L, temp(L ∧ R)],
	NextStep = (((A, P) ⊢ L) ∧ ((A, P1) ⊢ R)),

	
	U := A ∪ P,
	not(has_contradictions(U)),
	merge_rule([L, R], L ∧ R, "∧I", GIn, GOut).

% Same as
% A;P?L↔R → A;P?L→R and A;P?R→L   
% RuleName: ↔I
rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A, P) ⊢ (L ↔ R)), P1 := P ∪ [L → R, temp(L ↔ R)],
	NextStep = (((A, P) ⊢ (L → R)) ∧ ((A, P1) ⊢ (R → L))),
	
	U := A ∪ P,
	not(has_contradictions(U)),
	merge_rule([L → R, R → L], L ↔ R, "↔I", GIn, GOut).

% Same as
% [A;P?L→R] L ∈ (A ∪ P) → A;P?R   
%    with
% RuleName: →I
rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A, P) ⊢ (L → R)), 
	U:= A ∪ P, L ∈ U, Pn := P ∪ [temp(L → R)],
	NextStep = ((A, Pn) ⊢ R), 

	not(has_contradictions(U)),
	merge_rule([L, R], L → R, "→I", GIn, GOut).

% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), L ∉ (A ∪ P)] → A;P,L?C   
%    with
% RuleName: ∧E
rule(Origin, NextStep, GIn, GOut) :- 
	Origin = ((A, P1) ⊢ C), NextStep = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(L ∉ U), temp(L ∧ R) ∉ U, temp(L) ∉ U, P2 := P1 ∪ [L],

	not(has_contradictions(U)),
	derivation_route(C, L),
	merge_rule([L ∧ R], L, "∧E", GIn, GOut).




% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;P,R?C   
%    with
% RuleName: ∧E
rule(Origin, NextStep, GIn, GOut) :- 
	Origin = ((A, P1) ⊢ C), NextStep = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(R ∉ U), temp(L ∧ R) ∉ U, temp(R) ∉ U, P2 := P1 ∪ [R],
	
	not(has_contradictions(U)),
	derivation_route(C, R),

	merge_rule([L ∧ R], R, "∧E", GIn, GOut).


% Same as
% [A;P?C, (L ↔ R) ∈ (A ∪ P), (L → R) ∧ (R → L) ∉ (A ∪ P)] → A;P,(L → R) ∧ (R → L)?C   
%    with
% RuleName: ↔E
rule(Origin, NextStep, GIn, GOut) :- 
	Origin = ((A, P1) ⊢ C), NextStep = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ↔ R) ∈ U),
	(((L → R) ∧ (R → L)) ∉ U), temp(L ↔ R) ∉ U, temp(((L → R) ∧ (R → L))) ∉ U, P2 := P1 ∪ [(L → R) ∧ (R → L)],

	not(has_contradictions(U)),
	merge_rule([L ↔ R], (L → R) ∧ (R → L), "↔E", GIn, GOut).


%
% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L    
% RuleName: →E
rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A1, P1) ⊢ C), 
	NextStep = (((A2, P2) ⊢ L) ∧ ((A2, P3) ⊢ C)),
	GIn = graph(_, E),

	U1 := (A1 ∪ P1), ((L → R) ∈ U1), R ∉ U1, not(C=L), temp(L → R) ∉ U1, temp(R) ∉ U1,
	replace(L → R, temp(L → R), A1, A2), replace(L → R, temp(L → R), P1, P2), P3 := P2 ∪ [L, R],

	not(((¬(¬(L)) ∈ U1), (edge(¬(¬(L)), ¬(L), "¬E") ∈ E))), % To eliminate derivations like d ⊢ ¬(¬d)
	not(( L = ¬(¬(L1)), (edge(¬(¬(L1)), ¬(L1), "¬I") ∈ E))),% To eliminate derivations like ¬(¬d) ⊢ d

	not(has_contradictions(U1)),
	merge_rule([L, L → R], R, "→E", GIn, GOut).


%
% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P)] → A\(L ∨ R),P\(L ∨ R)?((L → C) ∧ (R → C))    
% RuleName: ∨E
rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A1, P1) ⊢ C), 
	NextStep = (((A2, P2) ⊢ (L → C)) ∧ ((A2, P2) ⊢ (R → C))),
	
	U1 := (A1 ∪ P1), ((L ∨ R) ∈ U1), temp(L ∨ R) ∉ U1,
	replace(L ∨ R, temp(L ∨ R), A1, A2), replace(L ∨ R, temp(L ∨ R), P1, P2),

	not(has_contradictions(U1)),

	merge_rule([L ∨ R, L → C, R → C], C, "∨E", GIn, GOut).


% Same as
% [A;P?L→R] → A,L;P?R   
%    with
% RuleName: →I
c_rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A1, P) ⊢ (L → R)),
	U:= A1 ∪ P, L ∉ U, A2 := A1 ∪ [L], Pn := P ∪ [temp(L → R)],%, [A1, P]], 
	NextStep = ((A2, Pn) ⊢ R),

	not(has_contradictions(U)),
	merge_rule([R], L → R, "→I", GIn, GOut).



% Same as
% [A;P?L∨R,] → [A;P?L]   
%    with
% RuleName: ∨I
c_rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ L), 
	U:= A ∪ P, 

	not(has_contradictions(U)),
	merge_rule([L], L ∨ R, "∨I", GIn, GOut).

% Same as
% [A;P?L∨R] → [A;P?R]   
%    with
% RuleName: ∨I
c_rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ R), 
	U:= A ∪ P, 

	not(has_contradictions(U)),
	merge_rule([R], L ∨ R, "∨I", GIn, GOut).




% Same as
% [A;P?C, (C ∧ ¬C) ∉ A, ¬C ∉ A] → (A,¬C;P?(X1 ∧ ¬X1)) ∨ (A,¬C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,¬C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬E 
% Remark: maybe its better to say ¬Xi ∈ (A ∪ P ∪ {¬C}), but already no counterexample for ¬Xi ∈ (A ∪ P) found.
c_rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A, P) ⊢ C), GIn = graph(V, _),
	not(is_contradiction(C)), U:= A ∪ P, (¬(C) ∉ U), (temp(¬(C)) ∉ U), A0 := A ∪ [¬(C)], 
	once((⊥(N), (⊥(N) ∉ V))),
	NextStep = ((A0, P) ⊢ ⊥(N)),

	merge_rule([¬(C), ⊥(N)], C, "¬E", GIn, GOut).


% Same as
% [A;P?¬C, (C ∧ ¬C) ∉ A, C ∉ A] → (A,C;P?(X1 ∧ ¬X1)) ∨ (A,C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬I 
c_rule(Origin, NextStep, GIn, GOut) :-
	Origin = ((A, P) ⊢ ¬(C)), GIn = graph(V, _),
	not(is_contradiction(C)), U:= A ∪ P, (C ∉ U), (temp(C) ∉ U), A0 := A ∪ [C],
	once((⊥(N), (⊥(N) ∉ V))),
	NextStep = ((A0, P) ⊢ ⊥(N)),

	merge_rule([C, ⊥(N)], ¬(C), "¬I", GIn, GOut).


%
% Proofs some Derivation
%

% Preconditions

proof(Derivation, Proof, Proof) :- 	
		isvalid(Derivation),!.
proof(Derivation, ProofIn, ProofOut) :- 	
		Derivation = ((_, _) ⊢ ⊥(N)),
		iscontradiction(Derivation, C),
		replace_vertex_weighted(⊥(N), (C ∧ ¬(C)), ProofIn, Proof0),
		merge_rule([C, ¬(C)], (C ∧ ¬(C)), "∧I", Proof0, ProofOut),
		
		!.
proof(Derivation, ProofIn, Proof) :- 
		Derivation = ((A, P) ⊢ C),
		U := (A ∪ P),
		not(has_cases(U, C)),
		rule(Derivation, NextStep, ProofIn, ProofOut),
		proof(NextStep, ProofOut, Proof),!.

proof(Derivation, ProofIn, Proof) :- 
		c_rule(Derivation, NextStep, ProofIn, ProofOut), 
		proof(NextStep, ProofOut, Proof),!.

proof(Derivation, ProofIn, Proof) 	:- 	
		Derivation = (D1 ∧ D2),
		D1 = ((_, _) ⊢ _),
		D2 = ((_, _) ⊢ _),

		proof(D1, ProofIn, ProofOut),
		proof(D2, ProofOut, Proof).

proof(Derivation, Proof) :- 
	Derivation = (A ⊢ C),
	proof(((A, []) ⊢ C), graph([],[]), ProofOriginal),
	remove_not_sufficcient_vertices(C, ProofOriginal, Proof).


% Examples
% ?- proof((([¬(q),p→q], []) ⊢ ¬(p)), P).
% ?- proof(([p],[]) ⊢ ( (¬(q→r)→ ¬(p)) → (¬(r)→ ¬(q))), P).
%


proof_py(Derivation, GProof, TProof) :-
	proof(Derivation, GProofO), 
	proof_table(GProofO, TProofO),
	term_to_atom(GProofO, GProof),
	term_to_atom(TProofO, TProof).

proof_t(Derivation, Proof) :-
	proof(Derivation, Proof1),
	Proof = Proof1._.

go_proof1(G) :- proof(([p→q,p] ⊢ q), G).
go_proof10(G) :- proof(([p→(q→r)] ⊢ (q→(p→r))), G).
go_proof5(G, T) :- proof_py(([¬(q),p→q] ⊢ ¬(p)), G, T).	
go_proof13(G) :- proof(([(p ∧ q) → r] ⊢ (p → (q → r)) ), G).
go_proof25(G, T) :- proof_py(([p] ⊢ ((¬(q→r)→ ¬(p))→ (¬(r)→ ¬(q)))), G, T).


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