%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze


:- set_prolog_flag(optimise_unify, false).

:-use_module(my_trace).

:-use_module(list_helper).
:-use_module(set).
:-use_module(invariant).
:-use_module(proposition).
:-use_module(derivation).

:-use_module(graph_proof).

:-use_module(proof_table).


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
% Executes the rules in following order: epoc1, epoch2, epoch3, epoch4 etc.
% The parameter RuleInfo illustrates a list with following parameters:
%	RuleName 
%	Assumptions of Rule
%	Premisses to be used in Rule
% 	Conclusion of Rule

% Same as
% A;P?L↔R → A;P?L→R and A;P?R→L
% RuleName: ↔I
simplify_derivation(epoch1, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ (LR)), P1 := P ∪ [L → R], nonvar(LR), LR =.. [↔, L, R],
	NextStep = (((A, P) ⊢ (L → R)) ∧ ((A, P1) ⊢ (R → L))),

	RuleInfo = ["↔I", A, [L → R, R → L], L ↔ R].

% Same as
% [A;P?C, (L ↔ R) ∈ (A ∪ P), (L → R) ∧ (R → L) ∉ (A ∪ P)] → A;P,(L → R) ∧ (R → L)?C
%    with
% RuleName: ↔E
simplify_derivation(epoch1, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P1) ⊢ C), NextStep0 = ((A, P2) ⊢ C), nonvar(C),
	U:= A ∪ P1, ((L ↔ R) ∈ U),
	(((L → R) ∧ (R → L)) ∉ U), P2 := P1 ∪ [(L → R) ∧ (R → L)],

	replace_derivation_by_inv(L ↔ R, NextStep0, NextStep),

	temp_invariant(A, AI),
	RuleInfo = ["↔E", AI, [L ↔ R], (L → R) ∧ (R → L)].

% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), L ∉ (A ∪ P)] → A;P,L?C
%    with
% RuleName: ∧E
simplify_derivation(epoch1, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P1) ⊢ C), NextStep0 = ((A, P2) ⊢ C), nonvar(C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(L ∉ U), P2 := P1 ∪ [L],

	((R ∈ U) -> replace_derivation_by_inv(L ∧ R, NextStep0, NextStep);NextStep = NextStep0),

	temp_invariant(A, AI),
	RuleInfo = ["∧E", AI, [L ∧ R], L].

% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;P,R?C
%    with
% RuleName: ∧E
simplify_derivation(epoch1, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P1) ⊢ C), NextStep0 = ((A, P2) ⊢ C), nonvar(C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(R ∉ U), P2 := P1 ∪ [R],

	((L ∈ U) -> replace_derivation_by_inv(L ∧ R, NextStep0, NextStep);NextStep = NextStep0),

	temp_invariant(A, AI),
	RuleInfo = ["∧E", AI, [L ∧ R], R].

%
% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L
% RuleName: →E
simplify_derivation(epoch1, Origin, NextStep, RuleInfo) :-
	Origin = ((A1, P1) ⊢ C), nonvar(C),
	Origin0 = ((A2, P2) ⊢ C),
	NextStep = (((A2, P2) ⊢ L) ∧ ((A2, P3) ⊢ C)),


	U1 := (A1 ∪ P1), temp_invariant(U1, UT),

	((L → R) ∈ U1), L ∈ U1,  R ∉ UT, not(C=L),

	replace_derivation_by_inv(L → R, Origin, Origin0),
	union(P2, [L, R], P3),

	temp_invariant(A1, A1I),
	RuleInfo = ["→E", A1I, [L, L → R], R].

%
% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P)] → A\(L ∨ R),P\(L ∨ R)?((L → C) ∧ (R → C))
% RuleName: ∨E
simplify_derivation(epoch2, Origin, NextStep, RuleInfo) :-
	Origin = ((A1, P1) ⊢ C),
	Origin0 = ((A2, P2) ⊢ C),
	NextStep = (((A2, P2) ⊢ (L → C)) ∧ ((A2, P2) ⊢ (R → C))),

	U1 := (A1 ∪ P1), ((L ∨ R) ∈ U1),
	(L == C; R == C; (L → C) ∈ U1; (R → C) ∈ U1),


	replace_derivation_by_inv(L ∨ R, Origin, Origin0),


	temp_invariant(A1, A1I),
	RuleInfo = ["∨E", A1I, [L ∨ R, L → C, R → C], C].


% Same as
% [A;P?L∨R,] → [A;P?L]
%    with
% RuleName: ∨I
simplify_derivation(epoch2, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ L),
	U:= A ∪ P, temp_invariant(U, UT), L ∈ UT,


	temp_invariant(A, AI),
	RuleInfo = ["∨I", AI, [L], L∨R].

% Same as
% [A;P?L∨R] → [A;P?R]
%    with
% RuleName: ∨I
simplify_derivation(epoch2, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ R),
	U:= A ∪ P, temp_invariant(U, UT), R ∈ UT,

	temp_invariant(A, AI),
	RuleInfo = ["∨I", AI, [L], L∨R].


% Same as
% A;P?L∧R → A;P?L and A;P?R
% RuleName: ∧I
simplify_derivation(epoch2, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ (L ∧ R)),
	P1 := P ∪ [L],
	NextStep = (((A, P) ⊢ L) ∧ ((A, P1) ⊢ R)),

	temp_invariant(A, AI),
	RuleInfo = ["∧I", AI, [L, R], L∧R].


% Same as
% [A;P?L→R] → A,L;P?R
%    with
% RuleName: →I
simplify_derivation(epoch21, Origin, NextStep, RuleInfo) :-
	Origin = ((A1, P) ⊢ (L → R)),
	A2 := A1 ∪ [L], %Pn := P ∪ [temp(L → R)],%, [A1, P]],
	NextStep = ((A2, P) ⊢ R),

	temp_invariant(A2, A2I),
	RuleInfo = ["→I", A2I, [L, R], L→R].


%
% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P)] → A\(L ∨ R),P\(L ∨ R)?((L → C) ∧ (R → C))
% Remark: Its not possible to use this rule, if C will be shown by ¬I or ¬E.
% RuleName: ∨E
simplify_derivation(epoch3, Origin, NextStep, RuleInfo) :-
	Origin = ((A1, P1) ⊢ C),
	Origin0 = ((A2, P2) ⊢ C),
	NextStep = (((A2, P2) ⊢ (L → C)) ∧ ((A2, P2) ⊢ (R → C))),

	U1 := (A1 ∪ P1), ((L ∨ R) ∈ U1),

	replace_derivation_by_inv(L ∨ R, Origin, Origin0),

	temp_invariant(A1, A1I),
	RuleInfo = ["∨E", A1I, [L ∨ R, L → C, R → C], C].


% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P)] → A\(L ∨ R),P\(L ∨ R)?((L → C) ∧ (R → C))
% RuleName: ∨E
simplify_derivation(epoch3, Origin, NextStep, []) :-
	C = ¬(L∨R), 
	Origin = ((A1, P1) ⊢ C),
	Origin0 = ((A2, P2) ⊢ C),
	NextStep = (((A1, P1) ⊢ D) ∧ ((A2, P3) ⊢ C)),
	get_np(L, NL), get_np(R, NR),
	D = ¬(NL ∧ NR),

	U1 := (A1 ∪ P1), ((L ∨ R) ∈ U1),

	replace_derivation_by_inv(L ∨ R, Origin, Origin0),
	P3 := P2 ∪ [D].


%	remove_inv(A1, A3, temp),
%	table_insert("Single", A3, _, D, TIn, TOut).

% Same as
% [A;P?L∨R,] → [A;P?L]
%    with
% RuleName: ∨I
simplify_derivation(epoch3, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ L),

	temp_invariant(A, AI),
	RuleInfo = ["∨I", AI, [L], L∨R].


% Same as
% [A;P?L∨R] → [A;P?R]
%    with
% RuleName: ∨I
simplify_derivation(epoch3, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ R),

	temp_invariant(A, AI),

	RuleInfo = ["∨I", AI, [R], L∨R].



% Same as
% [A;P?¬C, (C ∧ ¬C) ∉ A, C ∉ A] → (A,C;P?(X1 ∧ ¬X1)) ∨ (A,C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,C;P?(Xn ∧ ¬Xn))
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬I
simplify_derivation(epoch4, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ ¬(C)),
	%U:= A ∪ P,
	 (C ∉ A), (temp(C) ∉ A), A0 := A ∪ [C],
	NextStep = ((A0, P) ⊢ ¬(C)),

	temp_invariant(A0, AI),
	RuleInfo = ["¬I", AI, [C], ¬(C)].


% Same as
% [A;P?C, (C ∧ ¬C) ∉ A, ¬C ∉ A] → (A,¬C;P?(X1 ∧ ¬X1)) ∨ (A,¬C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,¬C;P?(Xn ∧ ¬Xn))
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬E
% Remark: maybe its better to say ¬Xi ∈ (A ∪ P ∪ {¬C}), but already no counterexample for ¬Xi ∈ (A ∪ P) found.
simplify_derivation(epoch4, Origin, NextStep, RuleInfo) :-
	Origin = ((A, P) ⊢ C),
	%U:= A ∪ P, 
	(¬(C) ∉ A), (temp(¬(C)) ∉ A), A0 := A ∪ [¬(C)],
	NextStep = ((A0, P) ⊢ C),

	temp_invariant(A0, AI),
	RuleInfo = ["¬E", AI, [¬(C)], C].


%
% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L
% RuleName: →E
/*simplify_derivation(epoch5, Origin, NextStep, []) :-
	Origin = ((A1, P1) ⊢ C),
	Origin0 = ((A2, P2) ⊢ C),
	NextStep = (((A2, P2) ⊢ L) ∧ ((A1, P3) ⊢ C)),

	U1 := (A1 ∪ P1), temp_invariant(U1, UT),

	((L → R) ∈ U1), R ∉ UT, not(C=L),

	replace_derivation_by_inv(L → R, Origin, Origin0),
	union([L], P1, P3),

	not(((¬(¬(L)) ∈ UT), (edge(¬(¬(L)), ¬(L), "¬E") ∈ E))), % To eliminate derivations like d ⊢ ¬(¬d)
	not(( L = ¬(¬(L1)), (edge(¬(¬(L1)), ¬(L1), "¬I") ∈ E))),% To eliminate derivations like ¬(¬d) ⊢ d

	remove_inv(A2, A3, temp),
	table_insert("Single", A3, _, L, TblIn, TblOut).
	%table_insert("→E", A3, [L, L → R], R, TIn, TOut).

%
% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∧Y, X,Y∈(A ∪ P) → A;R,P?D and A;P, D?C
simplify_derivation(epoch6, Origin, NextStep, []) :-
	Origin = ((A, P) ⊢ C),
	NextStep = (((A, P) ⊢ D) ∧ ((A, P1) ⊢ C)),

	U1 := (A ∪ P), temp_invariant(U1, UT),

	(¬(D) ∈ UT), D ∉ UT, not(C=D), D = (X∧Y), X ∈ UT, Y ∈ UT,
	P1 := P ∪ [D],

	remove_inv(A, A1, temp),
	table_insert("Single", A1, _, D, TblIn, TblOut).

% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∨Y, X or Y∈(A ∪ P) → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin   = ((A, P) ⊢ C),
	NextStep = (((A, P) ⊢ D) ∧ ((A, P1) ⊢ C)),


	U1 := (A ∪ P), temp_invariant(U1, UT),

	(¬(D) ∈ UT), D ∉ UT, D = (X∨Y), (X ∈ UT; Y ∈ UT),
	P1 := P ∪ [D].
	%not(C=D),

%	temp_invariant(A, A1),
%	table_insert("Single", A1, _, D, TblIn, TblOut).


% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X→Y, X or Y∈(A ∪ P) → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin   = ((A, P) ⊢ C),
	NextStep = (((A, P) ⊢ D) ∧ ((A, P1) ⊢ C)),


	U1 := (A ∪ P), temp_invariant(U1, UT),

	(¬(D) ∈ U1), D ∉ U1, not(C=D), D = (X→Y), (¬(X) ∈ UT; Y ∈ UT),
	P1 := P ∪ [D].

%	remove_inv(A, A1, temp),
%	table_insert("Single", A1, _, D, TblIn, TblOut).

% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∨Y → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin = ((A, P) ⊢ C),

	temp_invariant(A, AT), temp_invariant(P, PT),

	UT := (AT ∪ PT), U1 := (A ∪ P),

	(¬(D) ∈ U1), D ∉ U1, D = (X0∨Y0), get_np(X0, X), get_np(Y0, Y), (X∧Y) ∉ UT,
	P1 := P ∪ [X∧Y],

	tbl_assumptions_from_proposition(¬(D), AT, PT, TblIn, AGet, PGet),
	temp(AGet, A0), temp(PGet, P0),
	NextStep = (((A0, P0) ⊢ (X∧Y)) ∧ ((A, P1) ⊢ C)),

	table_insert("SingleR", AGet, _, (X∧Y), TblIn, TblOut).


% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∨Y → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin = ((A, P) ⊢ C),

	temp_invariant(A, AT), temp_invariant(P, PT),

	UT := (AT ∪ PT), U1 := (A ∪ P),

	(¬(D) ∈ U1), D ∉ U1, D = (X0∨Y0), get_np(X0, X), get_np(Y0, Y), (X∧Y) ∉ UT,
	P1 := P ∪ [X∧Y],

	tbl_assumptions_from_proposition(¬(D), AT, PT, TblIn, AGet, _),
	NextStep = ((A, P1) ⊢ C),

	table_insert("SingleL", AGet, _, (X∧Y), TblIn, TblOut).

% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∨Y → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin = ((A, P) ⊢ C),

	temp_invariant(A, AT), temp_invariant(P, PT),

	UT := (AT ∪ PT), U1 := (A ∪ P),

	(¬(D) ∈ U1), D ∉ U1, D = (X0∧Y0), get_np(X0, X), get_np(Y0, Y), (X∨Y)∉ UT,
	P1 := P ∪ [X∨Y],

	tbl_assumptions_from_proposition(¬(D), AT, PT, TblIn, AGet, PGet),
	temp(AGet, A0), temp(PGet, P0),
	NextStep = (((A0, P0) ⊢ (X∨Y)) ∧ ((A, P1) ⊢ C)),

	table_insert("SingleR", AGet, _, (X∨Y), TblIn, TblOut).

% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∨Y → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin = ((A, P) ⊢ C),

	temp_invariant(A, AT), temp_invariant(P, PT),

	UT := (AT ∪ PT), U1 := (A ∪ P),

	(¬(D) ∈ U1), D ∉ U1, D = (X0∧Y0), get_np(X0, X), get_np(Y0, Y), (X∨Y)∉ UT,
	P1 := P ∪ [X∨Y],

	tbl_assumptions_from_proposition(¬(D), AT, PT, TblIn, AGet, _),

	NextStep = ((A, P1) ⊢ C),

	table_insert("SingleL", AGet, _, (X∨Y), TblIn, TblOut).



% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∨Y → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin = ((A, P) ⊢ C),

	temp_invariant(A, AT), temp_invariant(P, PT),


	UT := (AT ∪ PT), U1 := (A ∪ P),

	(¬(D) ∈ UT), D ∉ U1, D = (X0→Y0), get_np(X0, X), get_np(Y0, Y), (X→Y)∉ UT,
	P1 := P ∪ [X→Y],

	tbl_assumptions_from_proposition(¬(D), AT, PT, TblIn, AGet, PGet),
	temp(AGet, A0), temp(PGet, P0),
	NextStep = (((A0, P0) ⊢ (X→Y)) ∧ ((A, P1) ⊢ C)),

	table_insert("SingleR", AGet, _, (X→Y), TblIn, TblOut).

% Same as
% [A;P?C, ¬(D) ∈ (A ∪ P), ¬(D) ≠ C, D = X∨Y → A;R,P?D and A;P, D?C
rule(epoch6, Origin, NextStep, []) :-
	Origin = ((A, P) ⊢ C),

	temp_invariant(A, AT), temp_invariant(P, PT),


	UT := (AT ∪ PT), U1 := (A ∪ P),

	(¬(D) ∈ UT), D ∉ U1, D = (X0→Y0), get_np(X0, X), get_np(Y0, Y), (X→Y)∉ UT,
	P1 := P ∪ [X→Y],


	tbl_assumptions_from_proposition(¬(D), AT, PT, TblIn, AGet, _),
	NextStep = ((A, P1) ⊢ C),

	table_insert("SingleL", AGet, _, (X→Y), TblIn, TblOut).



solvable_unless(N, Derivation, Graph, Table) :-
	M is N - 1,	get_atom_list_with_prefix_between(epoch, 1, M, Epochs),
	member(Epoch, Epochs), rule(Epoch, Derivation, _, Graph, _, Table, _).
*/

extend_table(RuleInfo, Line, TIn, TOut) :-
	RuleInfo = [RName, Assumptions, Premisses, Conclusion],
	table_insert(Assumptions, Premisses, RName, Conclusion, Line, TIn, TOut).

extend_graph(RuleInfo, GIn, GOut) :-
	RuleInfo = [RName, _, Premisses, Conclusion],
	merge_rule_graph(Premisses, Conclusion, RName, GIn, GOut).


%
% Proofs some Derivation
%

% Preconditions

extend_and_proof(Epoch, Derivation, GIn, GOut, TIn, TOut, ProofInfo) :-
	simplify_derivation(Epoch, Derivation, NextStep, RuleInfo),
	extend_table(RuleInfo, _, TIn, T),
	extend_graph(RuleInfo, GIn, G),
	trace_constant(epoch1, Derivation),
	trace_constant('Next Step', NextStep),
	inc_space_counter,
	proof(NextStep, G, GOut, T, TOut, ProofInfo),
	dec_space_counter,
	!.


proof_and_extend(Epoch, Derivation, GIn, GOut, TIn, TOut, ProofInfo) :-
	simplify_derivation(Epoch, Derivation, NextStep, RuleInfo),
	trace_constant(Epoch, Derivation),
	trace_constant('Next Step', NextStep),
	inc_space_counter,
	proof(NextStep, GIn, G, TIn, T, ProofInfo),
	extend_graph(RuleInfo, G, GOut),
	extend_table(RuleInfo, _, T, TOut),
	dec_space_counter,
	!.

assume_proof_and_extend_neg(Epoch, Derivation, GIn, GOut, TIn, TOut, [C]) :-
	simplify_derivation(Epoch, Derivation, NextStep, RuleInfo),
	trace_constant(Epoch, Derivation),
	trace_constant('Next Step', NextStep),
	inc_space_counter,
	RuleInfo = [X1, X2, [A], X3],
	assume(A, TIn, TA),
	proof(NextStep, GIn, G, TA, T, [C]),
	RuleInfoM = [X1, X2, [A, C], X3],
	extend_graph(RuleInfoM, G, GOut),
	extend_table(RuleInfoM, L, T, T0),
	remove_assumption(A, L, T0, TOut),
	dec_space_counter,
	!.

assume_proof_and_extend_imp(Epoch, Derivation, GIn, GOut, TIn, TOut, [C]) :-
	simplify_derivation(Epoch, Derivation, NextStep, RuleInfo),
	trace_constant(Epoch, Derivation),
	trace_constant('Next Step', NextStep),
	inc_space_counter,
	RuleInfo = [X1, X2, [A], X3],
	assume(A, TIn, TA),
	proof(NextStep, GIn, G, TA, T, _),
	extend_graph(RuleInfo, G, GOut),
	extend_table(RuleInfo, L, T, T0),
	remove_assumption(A, L, T0, TOut),
	dec_space_counter,
	!.



proof(Derivation, GIn, GOut, TIn, TOut, [(¬(X) ∧ X)]) :-
		Derivation = ((A, P) ⊢ C),
		DerivationI = ((AI, PI) ⊢ C),
		temp_invariant(A, AI), temp_invariant(P, PI),
		iscontradiction(DerivationI, X),
		merge_rule_graph([¬(X), X], (¬(X) ∧ X), "∧I", GIn, GOut),
		table_insert(AI, [¬(X), X], "∧I", ¬(X) ∧ X, _, TIn, TOut),


		%table_insert("⊥", AA, [¬(X), X, ¬(X) ∧ X, N], C, TIn, TOut),
		!.
proof(Derivation, G, G, T, T, []) :-
		Derivation = ((A, P) ⊢ C),
		DerivationI = ((AI, PI) ⊢ C),
		temp_invariant(A, AI), temp_invariant(P, PI),
		isvalid(DerivationI),
		!.
proof(Derivation, GIn, GOut, TIn, TOut, ProofInfo) :-
		extend_and_proof(epoch1, Derivation, GIn, GOut, TIn, TOut, ProofInfo).
proof(Derivation, GIn, GOut, TIn, TOut, ProofInfo) :-
		proof_and_extend(epoch2, Derivation, GIn, GOut, TIn, TOut, ProofInfo).
proof(Derivation, GIn, GOut, TIn, TOut, ProofInfo) :-
		assume_proof_and_extend_imp(epoch21, Derivation, GIn, GOut, TIn, TOut, ProofInfo).
proof(Derivation, GIn, GOut, TIn, TOut, ProofInfo) :-
		assume_proof_and_extend_neg(epoch4, Derivation, GIn, GOut, TIn, TOut, ProofInfo).


/*proof(Derivation, GIn, G, TIn, T) :-
		rule(epoch2,Derivation, NextStep, GIn, GOut, TIn, TOut),
		trace_constant(epoch2, Derivation),
		trace_constant('Next Step', NextStep),
		inc_space_counter,
		proof(NextStep, GOut, G, TOut, T),
		dec_space_counter,
		!.
proof(Derivation, GIn, G, TIn, T) :-
		rule(epoch3,Derivation, NextStep, GIn, GOut, TIn, TOut),
		trace_constant(epoch3, Derivation),
		trace_constant('Next Step', NextStep),
		trace_nl,
		inc_space_counter,
		proof(NextStep, GOut, G, TOut, T),
		dec_space_counter,
		!.
proof(Derivation, GIn, G, TIn, T) :-
		not(solvable_unless(3, Derivation, GIn, TIn)),
		rule(epoch4,Derivation, NextStep, GIn, GOut, TIn, TOut),
		trace_constant(epoch4, Derivation),
		trace_constant('Next Step', NextStep),
		inc_space_counter,
		proof(NextStep, GOut, G, TOut, T),
		dec_space_counter,
		!.
proof(Derivation, GIn, G, TIn, T) :-
		not(solvable_unless(5, Derivation, GIn, TIn)),
		rule(epoch5,Derivation, NextStep, GIn, GOut, TIn, TOut),
		trace_constant(epoch5, Derivation),
		trace_constant('Next Step', NextStep),
		inc_space_counter,
		proof(NextStep, GOut, G, TOut, T),
		dec_space_counter,!.
proof(Derivation, GIn, GOut, TIn, TOut) :-
		not(solvable_unless(6, Derivation, GIn, TIn)),
		rule(epoch6,Derivation, NextStep, GIn, GIn, TIn, TB),
		trace_constant(epoch6, Derivation),
		trace_constant('Next Step', NextStep),
		inc_space_counter,
		proof(NextStep, GIn, GOut, TB, TOut),
		dec_space_counter,!.*/
proof(Derivation, GIn, G, TIn, T, ProofInfo) 	:-
		Derivation = (D1 ∧ D2),
		D1 = ((_, _) ⊢ _),
		D2 = ((_, _) ⊢ _),

		trace_constant('Split', Derivation),
		trace_constant('Split1', D1),
		inc_space_counter,
		proof(D1, GIn, GOut, TIn, TB, _), dec_space_counter, %complete_subproof(TB, TOut),
		trace_constant('Split2', D2),
		inc_space_counter,
		proof(D2, GOut, G, TB, T, ProofInfo), dec_space_counter.

proof(Derivation, Graph, Table) :-
	Derivation = (A ⊢ C),
	table_init(A, TInit),
	proof(((A, []) ⊢ C), graph([],[]), Graph0, TInit, Table, _),
	%define_table(Table0, Table),
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
	trace_constant('To prove',Derivation),
	inc_space_counter,
	format('To prove: ~w~n', [Derivation]),
	proof(Derivation, Graph, Table).

go_proof1(G, T) :- proofD(([p→q,p] ⊢ q), G, T).
go_proof2(G, T) :- proofD(([(¬q),((¬q)→((¬p)→q))] ⊢ ((¬p)→q)), G, T).
go_proof3(G, T) :- proofD(([p→q,q→r,p] ⊢ r), G, T).
go_proof4(G, T) :- proofD(([p→(q→r),p→q,p] ⊢ r), G, T).
go_proof5(G, T) :- proofD(([¬(q),p→q] ⊢ ¬(p)), G, T).
go_proof6(G, T) :- proofD(([p→(q→r),p,¬(r)] ⊢ ¬(q)), G, T).
go_proof8(G, T) :- proofD(([¬(p)→q,¬(q)] ⊢ p), G, T).
go_proof9(G, T) :- proofD(([p→q] ⊢ (¬(q)→ ¬(p))), G, T).
go_proof10(G, T) :- proofD(([p→(q→r)] ⊢ (q→(p→r))), G, T).
go_proof11(G, T) :- proofD(([q→r] ⊢ ((¬(q)→ ¬(p))→ (p→r))), G, T).
go_proof12(G, T) :- proofD(([p→ ¬(q), q] ⊢ ¬(p)), G, T).

go_proof13(G, T) :- proofD(([(p ∧ q) → r] ⊢ (p → (q → r)) ), G, T).
go_proof13_2(G,T) :- proofD(([q → (p → r), ¬(r), q] ⊢ ¬(p)), G, T).

go_proof14(G, T) :- proofD(([p → ¬(¬(q)), p] ⊢ q), G, T).

go_proof22(G, T) :- proofD(([(p → (q → (r → s)))] ⊢ (r → (p → (q → s)))), G, T).
go_proof25(G, T) :- proofD(([p] ⊢ ((¬(q→r)→ ¬(p))→ (¬(r)→ ¬(q)))), G, T).
go_proof28(G, T) :- proofD(([(p ∧ q)] ⊢ p), G, T).


go_proof31(G, T) :- proofD(([q → r] ⊢ ((p ∧ q) → (p ∧ r))), G, T).
go_proof32(G, T) :- proofD(([(p ∧ q)] ⊢ (q ∧ p)), G, T).
go_proof33(G, T) :- proofD(([(p∨q)] ⊢ (q∨p)), G, T).
go_proof34(G, T) :- proofD(([(q→r)] ⊢ ((p∨q)→(p∨r))), G, T).
go_proof35(G, T) :- proofD(([(p∨(q∨r))] ⊢ (q∨(p∨r))), G, T).
go_proof41(G, T) :- proofD(([(p∧q)] ⊢ (p∨q)), G, T).
go_proof42(G, T) :- proofD(([(p→r)∧(q→r)] ⊢ ((p∨q)→r)), G, T).
go_proof44(G, T) :- proofD(([(p→q),(r→s)] ⊢ ((p∨r)→(q∨s))), G, T).
go_proof46(G, T) :- proofD(([p→(q∧r)] ⊢ ((p→q)∧(p→r))), G, T).
go_proof48(G, T) :- proofD(([(p↔q)] ⊢ (q↔p)), G, T).
go_proof50(G, T) :- proofD(([(p↔q),(q↔r)] ⊢ (p↔r)), G, T).
go_proof54(G, T) :- proofD([(p↔q)] ⊢ ((¬p)↔(¬q)), G, T).
go_proof58(G, T) :- proofD([(p↔(¬q)), (q↔(¬r))] ⊢ (p↔r), G, T).
go_proof64(G, T) :- proofD([(p∨(p∧q))] ⊢ p, G, T).
go_proof68(G, T) :- proofD([p, (¬(p∧q))] ⊢ (¬q), G, T).
go_proof69(G, T) :- proofD([(p→q)] ⊢ (¬(p∧(¬q))), G, T).
go_proof72(G, T) :- proofD([(¬((¬p)∧(¬q)))] ⊢ (p∨q), G, T).
go_proof72_3a(G, T) :- proofD([(p∧(q∨r))] ⊢ ((p∧q)∨(p∧r)), G, T).
go_proof72_3b(G, T) :- proofD([((p∧q)∨(p∧r))] ⊢ (p∧(q∨r)), G, T).
go_proof72_5b(G, T) :- proofD([(¬(p→(¬q)))] ⊢ (p∧q), G, T).
go_proof72_6b(G, T) :- proofD([((¬p)∧(¬q))] ⊢ (¬(p∨q)), G, T).
go_proof72_8a(G, T) :- proofD([(p∧q)] ⊢ (¬((¬p)∨(¬q))), G, T).
go_proof72_9a(G, T) :- proofD([(p→q)] ⊢ (¬(p)∨q), G, T).

go_proof_37a(G, T) :- proofD([] ⊢ (¬(p∧(¬p))), G, T).
go_proof_37b(G, T) :- proofD([] ⊢ (¬(¬(p)∧p)), G, T).
go_proof_44(G, T) :- proofD([] ⊢ (p∨(¬p)), G, T).
go_proof_45(G, T) :- proofD([p] ⊢ ((p∧q)∨(p∧(¬q))), G, T).

go_proof_test(G, T) :- proofD([((¬p)∨q)] ⊢ (p→q), G, T).
go_proof_test2(G, T) :- proofD([p] ⊢ (q→q), G, T).
go_proof_test3(G, T) :- proofD([¬(p∨q)] ⊢ ((¬p)∧(¬q)), G, T).

% Testfunktion zum Überprüfen des Einlesens der Datei
test_read_file :-
    FileName = '../data/problems.txt',
    print_all_lines(FileName).


go_debug :-
    set_prolog_flag(color_term, false),
    protocol('p.txt'),
    leash(-all),
    trace(proof/3),
    proof((([(p↔q), (q↔r)],[]) ⊢ (p↔r)), _G, _P),
    !,
    nodebug,
    noprotocol.
go_debug :-
    nodebug,
    noprotocol.
