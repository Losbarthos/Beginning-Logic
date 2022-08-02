%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze


:- set_prolog_flag(optimise_unify, false).

:-use_module(set).
:-use_module(invariant).
:-use_module(proposition).
:-use_module(derivation).

:-use_module(ldict).

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
	is_list(Term),
	write_term(Term, [max_depth(0)]).

%
% Derivations which can used in the proof.
%

% Same as
% A;P?L∧R → A;P?L and A;P?R   
% RuleName: ∧I
rule(Origin, NextStep, DictIn, DictOut, 0) :-
	Origin = ((A, P) ⊢ (L ∧ R)), P1 := P ∪ [L, temp(L ∧ R)],
	NextStep = (((A, P) ⊢ L) ∧ ((A, P1) ⊢ R)),
	
	U := A ∪ P,
	not(has_contradictions(U)),

	%%
	% Filling DictOut
	%%
	temp_invariant(A, Ai),
	Assumptions = Ai,
	PremissesOrigin = [L, R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L ∧ R],
	Rule = "∧I",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,


	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).

% Same as
% [A;P?L→R] L ∈ (A ∪ P) → A;P?R   
%    with
% RuleName: →I
rule(Origin, NextStep, DictIn, DictOut, _) :-
	Origin = ((A, P) ⊢ (L → R)), 
	U:= A ∪ P, L ∈ U, Pn := P ∪ [temp(L → R)],
	NextStep = ((A, Pn) ⊢ R), 

	not(has_contradictions(U)),

	%%
	% Filling DictOut
	%%
	temp_invariant(A, Ai),
	Assumptions = Ai,
	PremissesOrigin = [L, R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L → R],
	Rule = "→I",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,

	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						    Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).

% Same as
% [A;P?L→R] → A,L;P?R   
%    with
% RuleName: →I
rule(Origin, NextStep, DictIn, DictOut, _) :-
	Origin = ((A1, P) ⊢ (L → R)),
	U:= A1 ∪ P, L ∉ U, Pn := P ∪ [temp(L → R)], A2 := A1 ∪ [L],
	merge_premisses([A2, Pn], [_, MPn]),
	NextStep = ((A2, MPn) ⊢ R),

	not(has_contradictions(U)),
	
	%%
	% Filling DictOut
	%%
	temp_invariant(A2, A2i),
	Assumptions = A2i,
	PremissesOrigin = [R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [L],
	Conclusion = [L → R],
	Rule = "→I",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,

	dict_proof_append_assumption(L, DictIn, DictBuffer),
	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						    Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictBuffer, DictOut).


% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), L ∉ (A ∪ P)] → A;P,L   
%    with
% RuleName: ∧E
rule(Origin, NextStep, DictIn, DictOut, _) :- 
	Origin = ((A, P1) ⊢ C), NextStep = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(L ∉ U), temp(L ∧ R) ∉ U, temp(L) ∉ U, append(P1, [L], P2),

	not(has_contradictions(U)),
	derivation_route(C, L),

	%%
	% Filling DictOut
	%%
	temp_invariant(A, Ai),
	Assumptions = Ai,
	PremissesOrigin = [L ∧ R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L],
	Rule = "∧E",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,


	dict_proof_append_last(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).

% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;P,R   
%    with
% RuleName: ∧E
rule(Origin, NextStep, DictIn, DictOut, _) :- 
	Origin = ((A, P1) ⊢ C), NextStep = ((A, P2) ⊢ C),
	U:= A ∪ P1, ((L ∧ R) ∈ U),
	(R ∉ U), temp(L ∧ R) ∉ U, temp(R) ∉ U, append(P1, [R], P2),
	
	not(has_contradictions(U)),
	derivation_route(C, R),

	%%
	% Filling DictOut
	%%
	temp_invariant(A, Ai),
	Assumptions = Ai,
	PremissesOrigin = [L ∧ R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [R],
	Rule = "∧E",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,


	dict_proof_append_last(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).

%
% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L    
% RuleName: →E
rule(Origin, NextStep, DictIn, DictOut, 1) :-
	Origin = ((A1, P1) ⊢ C), 
	NextStep = (((A2, P2) ⊢ L) ∧ ((A2, P3) ⊢ C)),
	
	U1 := (A1 ∪ P1), ((L → R) ∈ U1), R ∉ U1, not(C=L), temp(L → R) ∉ U1, temp(R) ∉ U1,
	replace(L → R, temp(L → R), A1, A2), replace(L → R, temp(L → R), P1, P2), P3 := P2 ∪ [L, R],

	not(has_contradictions(U1)),
	derivation_route(C, R),


	%%
	% Filling DictOut
	%%
	temp_invariant(A1, A1i),
	Assumptions = A1i,
	PremissesOrigin = [L, L → R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [R],
	Rule = "→E",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,

	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).

%
% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P)] → A\(L ∨ R),P\(L ∨ R)?((L → C) ∧ (R → C))    
% RuleName: ∨E
rule(Origin, NextStep, DictIn, DictOut, 0) :-
	Origin = ((A1, P1) ⊢ C), 
	NextStep = (((A2, P2) ⊢ (L → C)) ∧ ((A2, P2) ⊢ (R → C))),
	
	U1 := (A1 ∪ P1), ((L ∨ R) ∈ U1), temp(L ∨ R) ∉ U1,
	replace(L ∨ R, temp(L ∨ R), A1, A2), replace(L ∨ R, temp(L ∨ R), P1, P2),

	not(has_contradictions(U1)),


	%%
	% Filling DictOut
	%%
	temp_invariant(A1, A1i),
	Assumptions = A1i,
	PremissesOrigin = [L ∨ R, L → C, R → C],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [C],
	Rule = "∨E",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,

	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).

% Same as
% [A;P?L∨R,] → [A;P?L]   
%    with
% RuleName: ∨I
c_rule(Origin, NextStep, DictIn, DictOut) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ L), 
	U:= A ∪ P, 

	not(has_contradictions(U)),
	%has_no_cases(U),

	%%
	% Filling DictOut
	%%
	temp_invariant(A, Ai),
	Assumptions = Ai,
	PremissesOrigin = [L],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L ∨ R],
	Rule = "∨I",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,

	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).

% Same as
% [A;P?L∨R] → [A;P?R]   
%    with
% RuleName: ∨I
c_rule(Origin, NextStep, DictIn, DictOut) :-
	Origin = ((A, P) ⊢ (L ∨ R)),
	NextStep = ((A, P) ⊢ R), 
	U:= A ∪ P, 

	not(has_contradictions(U)),
	%has_no_cases(U),

	%%
	% Filling DictOut
	%%
	temp_invariant(A, Ai),
	Assumptions = Ai,
	PremissesOrigin = [R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L ∨ R],
	Rule = "∨I",
	DerivationOrigin = Origin,
	DerivationNextStep = NextStep,

	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut).



% Same as
% [A;P?C, (C ∧ ¬C) ∉ A, ¬C ∉ A] → (A,¬C;P?(X1 ∧ ¬X1)) ∨ (A,¬C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,¬C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬E 
% Remark: maybe its better to say ¬Xi ∈ (A ∪ P ∪ {¬C}), but already no counterexample for ¬Xi ∈ (A ∪ P) found.
c_rule(Origin, NextStep, DictIn, DictOut, LastStep) :-
	Origin = ((A1, P1) ⊢ C), 
	LastStep = ((A1, P2) ⊢ C),
	not(⊥(C)), U:= A1 ∪ P1, (¬(C) ∉ U), (temp(¬(C)) ∉ U), A2 := A1 ∪ [¬(C)], P2 := P1 ∪ [C], not(anymember_invariant_2n(U, ¬(C), ¬)),
	U2 := A2 ∪ P1, contradictions(U2, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P1) ⊢ (Y ∧ ¬(Y)))), NextStepList),
	disjunction_list(NextStepList, NextStep),

	findall(X, (member(Y, Contra), 
				%%
				% Filling DictOut
				%%
				temp_invariant(A2, A2i),
				Assumptions = A2i,
				PremissesOrigin = [¬(C), Y ∧ ¬(Y)],
				PremissesNoOrigin = [],
				PremissesExcOrigin = [¬(C)],
				Conclusion = [C],
				Rule = "¬E",
				DerivationOrigin = Origin,
				DerivationNextStep = NextStep,

				dict_proof_append_assumption(¬(C), DictIn, XBuffer),
				dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, 
										PremissesExcOrigin,
										Conclusion, Rule, DerivationOrigin, DerivationNextStep, XBuffer, X)),
				NegEList),
	disjunction_list(NegEList, DictOut).

% Same as
% [A;P?¬C, (C ∧ ¬C) ∉ A, C ∉ A] → (A,C;P?(X1 ∧ ¬X1)) ∨ (A,C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬I 
c_rule(Origin, NextStep, DictIn, DictOut, LastStep) :-
	Origin = ((A1, P1) ⊢ ¬(C)), 
	LastStep = ((A1, P2) ⊢ ¬(C)),
	not(⊥(C)), U:= A1 ∪ P1, (C ∉ U), temp(C) ∉ U, A2 := A1 ∪ [C], P2 := P1 ∪ [¬(C)], not(anymember_invariant_2n(U, C, ¬)),
	U2 := A2 ∪ P1, contradictions(U2, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P1) ⊢ (Y ∧ ¬(Y)))), NextStepList),
	disjunction_list(NextStepList, NextStep),
	
	findall(X, (member(Y, Contra), 
				%%
				% Filling DictOut
				%%
				temp_invariant(A2, A2i),
				Assumptions = A2i,
				PremissesOrigin = [C, Y ∧ ¬(Y)],
				PremissesNoOrigin = [],
				PremissesExcOrigin = [C],
				Conclusion = [¬(C)],
				Rule = "¬I",
				DerivationOrigin = Origin,
				DerivationNextStep = NextStep,

				dict_proof_append_assumption(C, DictIn, XBuffer),
				dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, 
										PremissesExcOrigin,
										Conclusion, Rule, DerivationOrigin, DerivationNextStep, XBuffer, X)),
			NegIList),
	disjunction_list(NegIList, DictOut).


%
% Proofs some Derivation
%

% Preconditions

proof_rule(Derivation, NextStep, ProofIn, ProofOut, I) :- 	
		Derivation = ((A, P) ⊢ C),
		U := (A ∪ P),
		not(has_cases(U, C)),
		rule(Derivation, NextStep, ProofIn, ProofOut, I).

proof(Derivation, LastAssumptions, LastPremisses, Proof, Proof, _) :- 	
		Derivation = ((LastAssumptions, LastPremisses) ⊢ _),
		isvalid(Derivation),!.

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, _) :- 
		proof_rule(Derivation, NextStep, ProofIn, ProofOut, I),
		proof(NextStep, LastAssumptions, LastPremisses, ProofOut, Proof, I),!.

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, _) :- 
		c_rule(Derivation, NextStep, ProofIn, ProofOut), 
		proof(NextStep, LastAssumptions, LastPremisses, ProofOut, Proof, _),!.

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, _) :- 
		LastStep = ((LastAssumptions, LastPremisses) ⊢ _),
		c_rule(Derivation, NextStep, ProofIn, ProofOut, LastStep), 
		proof(NextStep, _, _, ProofOut, Proof, _).

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, _) :- 
		Derivation = (D1 ∨ _),
		ProofIn = (Proof1 ∨ _),
		proof(D1, LastAssumptions, LastPremisses, Proof1, Proof, _).
proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, _) :- 
		Derivation = (_ ∨ D2),
		ProofIn = (_ ∨ Proof2),
		proof(D2, LastAssumptions, LastPremisses, Proof2, Proof, _).
proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, I) 	:- 	
		Derivation = (D1 ∧ D2),
		D1 = ((A1, P1) ⊢ _),
		D2 = ((A1, P) ⊢ C),
		D3 = ((A1, P2) ⊢ C), 

		dict_min_index(ProofIn, MinIndex),
		IndexUntouched is MinIndex + I,

		proof(D1, A1L, P1L, ProofIn, ProofBetween1, _),
		Px := (P1 ∪ P) ∪ [[A1L, P1L]],
		merge_premisses([A1, Px], [A1, P2]),

		dict_normalize(ProofBetween1, IndexUntouched, ProofBetween2),

		proof(D3, LastAssumptions, LastPremisses, ProofBetween2, Proof, _).
proof(Derivation, Proof) :- 
	distinct([Proof], (Derivation = ((A, []) ⊢ _),
	dict_from_assumptions(A, Assumptions),
	proof(Derivation, _, _, Assumptions, ProofRaw, _),
	dict_normalize(ProofRaw, 1, Proof))).


% Examples
% ?- proof((([¬(q),p→q], []) ⊢ ¬(p)), P).
% ?- proof(([p],[]) ⊢ ( (¬(q→r)→ ¬(p)) → (¬(r)→ ¬(q))), P).
%


proof_py(Derivation, Proof) :-
	proof(Derivation, Proof1), 
	term_to_atom(Proof1, Proof).

proof_t(Derivation, Proof) :-
	proof(Derivation, Proof1),
	Proof = Proof1._.



go_debug :-
    set_prolog_flag(color_term, false),
    protocol('p.txt'),
    leash(-all),
    trace(proof/6),
    proof(([(p→(¬p))],[]) ⊢ (¬p), _P),
    !,
    nodebug,
    noprotocol.
go_debug :-
    nodebug,
    noprotocol.