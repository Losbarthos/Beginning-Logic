%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze


:- set_prolog_flag(optimise_unify, false).

:-use_module(ldict).
:-use_module(definitions).
:-use_module(library(http/json)).

% Logical operators
% Connectives
:-op(699, xfx, :=).

:-op(800, fx, ¬).
:-op(801, xfy, ∧).
:-op(802, xfy, ∨).
:-op(803, xfy, →).
:-op(804, xfy, ↔).
% Derivation symbol
:-op(799, xfy, ⊢).


% Operators to use for sets
:-op(599, xfy, ∈).
:-op(599, xfy, ∉).
:-op(598, xfy, ∪).
:-op(597, xfy, ∩).

binary_connective(X  ∨  Y, X, Y).
binary_connective(X  ∧  Y, X, Y).
binary_connective(X  → Y, X, Y).
binary_connective(X  ↔ Y, X, Y).
binary_derivation(X ⊢ Y, X, Y).
negation(¬(X), X).

% Definition of formulas used in propositional logic
formula(X) :-
    variable(X).
formula(Binary) :-
    binary_connective(Binary, X, Y),
    formula(X),
    formula(Y).
formula(¬ X) :-
    formula(X).

% Used as atoms or individual symbols
variable(p).
variable(q).
variable(r).

% Converts a list l1,...,ln into (l1 ∨ (l2 ∨ ( ... ∨ ln)...)
disjunction_list(List, Disjunction) :- 
	List = [Head | Tail], 
	disjunction_list(Tail, Sub),
	Disjunction = (Head ∨ Sub).
disjunction_list(List, Disjunction) :-
	List = [X], length(List, 1), Disjunction = X.

% Converts a list l1,...,ln into (l1 ∧ (l2 ∧ ( ... ∧ ln)...)
conjunction_list(List, Disjunction) :- 
	List = [Head | Tail], 
	disjunction_list(Tail, Sub),
	Disjunction = (Head ∧ Sub).
conjunction_list(List, Disjunction) :-
	List = [X], length(List, 1), Disjunction = X.

% Definition of subformula
subformulas(Formula, Subformulas) :- 
			variable(Formula), 
			Subformulas = [Formula].
subformulas(Formula, Subformulas) :-
			binary_connective(Formula, X, Y),
			subformulas(X, S1),
			subformulas(Y, S2),
			union(S1, S2, SXY),
			union(SXY,[Formula],Subformulas).

subformulas(Formula, Subformulas) :-
			Formula = ¬(X),
			subformulas(X, S1),
			union(S1, [¬(X)], Subformulas).


% We introduce some derivation symbol which is orientated on intercalation caluli 
% (see "Searching for Proogs (in Sentential Logic)" 
%	from Wilfried Sieg and Richard Scheines)

% Symbols used in set theory

% Definition of element
X ∈ M :- member(X, M).
X ∉ M :- not(member(X, M)).

union_((A ∪ B), C, D) :- union_(A, B, X), union_(X, C, D).
union_(A, (B ∪ C), D) :- union_((A ∪ B), C, D).
union_(A, B, C) :- is_list(A), is_list(B), union(A, B, C).

intersection_((A ∪ B), C, D) :- intersection_(A, B, X), intersection_(X, C, D).
intersection_(A, (B ∪ C), D) :- intersection_((A ∪ B), C, D).
intersection_(A, B, C) :- intersection(A, B, C).

C := (A ∪ B) :- union_(A, B, C).
C := (A ∩ B) :- intersection_(A, B, C).

% Definition of derivation
% We define some derivation as the same as the intercalation derivation 
Tail ⊢ Head :-
	Tail = (Assumptions, Premisses),
	formula(Head),
	forall(member(X,Assumptions), formula(X)),
	forall(member(X,Premisses), formula(X)).

derivation(X) :- X = (_ ⊢ _).
derivation(X) :- binary_connective(X, A, B), derivation(A), derivation(B).

% removes all elements from LIn, which are not derivations
find_derivations(LIn, LOut) :-
	findall(X, (X ∈ LIn, derivation(X)), LOut).


% extracts Assumptions, Premisses and Conclusion from derivation
unzip(Derivation, Assumptions, Premisses, Conclusion) :-
	Derivation = ((Assumptions, Premisses) ⊢ Conclusion).

% checks if a Derivation is valid without some use of proof steps
isvalid(((A, P) ⊢ C)) :-
	AP := A ∪ P,
	C ∈ AP.

% Contradiction rules
⊥(A):- A = (X ∧ ¬X), formula(X).
⊥(A):- A = (¬X ∧ X), formula(X).

% contradictions(+B, -C)
% Gets all possible contradictions withhin negation elemination and introduction

% The set of contradictions of A ∧ B, A ∨ B, A → C and A ↔ B is the union of the set of contradictions of A
% with the set of contradictions of B
contradictions(B, C) :-
	binary_connective(B, X, Y), 
	contradictions(X, C1), 
	contradictions(Y, C2), 
	C := C1 ∪ C2.
% The set of contradictions of a negation ¬ A only consists of ¬ A itself.
contradictions(B, C) :-
	B = ¬(A), 
	C = [A].
% The set of contradictions of some variable is empty.
contradictions(B, C) :-
	subformulas(B, S),
	findall(X, (X ∈ S, X = ¬(_)), Neg),
	length(Neg, 0), 
	C = [].
% Find all contradictions for some list of propositions.
contradictions(B, C) :-
	findall(X, (Y ∈ B, not(is_list(Y)), contradictions(Y, X)), SC),
	append(SC, C0), sort(C0, C).

% checks, if it is some derivation route from "From" to "To"
derivation_route(From, To) :-
	From = To.
derivation_route(From, To) :-
	binary_connective(To, X, _), derivation_route(From, X).
derivation_route(From, To) :-
	binary_connective(To, _, Y), derivation_route(From, Y).

% Checks whether a case C occurs as disjunct in the disjunction d1 ∨ d2 ∨ ... ∨ dn 
is_case_of(C, D) :-
	C = D.
is_case_of(C, D) :-
	D = (D1 ∨ _),
	is_case_of(C, D1).
is_case_of(C, D) :-
	D = (_ ∨ D2),
	is_case_of(C, D2).

% Checks if the set S has at least one X with is_case_of(X, D)
has_cases(S, D) :-
	member(X, S), is_case_of(X, D).

% checks, if the set S has contradictions. 
has_contradictions(S) :- A ∈ S, ¬(A) ∈ S.

% Checks, if some functor is negation invariant. More details see: 
% https://stackoverflow.com/questions/71967110/remove-invariants-from-some-prolog-list/71980981#71980981
% invariant_2n(+X,+Y,+Fun)

invariant_2n(X, Y, Fun) :-
    Y =.. [Fun, T],
    T =.. [Fun, X].
invariant_2n(X, Y, Fun) :-
    Y =.. [Fun, T],
    T =.. [Fun, Z],
    invariant_2n(X, Z, Fun).

% Checks, if their is some member in Terms, which has negation invariant opposite to Member 
% anymember_invariant_2n(+Terms,+Member,+F)
anymember_invariant_2n(Terms, Member, F) :-
	T ∈ Terms,
	invariant_2n(T, Member, F).
anymember_invariant_2n(Terms, Member, F) :-
	T ∈ Terms,
	invariant_2n(Member, T, F).

% Deletes all members of WithTemp with prefix temp(...). 
% no_temp(+WithTemp,-NoTemp)
no_temp(WithTemp, NoTemp) :-
	findall(X, (X ∈ WithTemp, not(X=temp(_))), NoTemp).

temp_invariant(WithTemp, TempInvariant) :-
	no_temp(WithTemp, NoTemp),
	findall(X, (temp(X) ∈ WithTemp), Invariant),
	TempInvariant := (NoTemp ∪ Invariant).



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
		%not(proof_rule(Derivation, _, ProofIn, _, _)),
		c_rule(Derivation, NextStep, ProofIn, ProofOut), 
		proof(NextStep, LastAssumptions, LastPremisses, ProofOut, Proof, _),!.

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, _) :- 
		LastStep = ((LastAssumptions, LastPremisses) ⊢ _),
		%not(proof_rule(Derivation, _, ProofIn, _, _)),
		%not(c_rule(Derivation, _, ProofIn, ProofOut)),
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
%proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof, I) 	:- 	
%		Derivation = (D1 ∧ D2),
%		D1 = ((A1, P1) ⊢ _),
%		D2 = ((A1, P2) ⊢ C),
%		D3 = (AP ⊢ C), 
%
%		dict_min_index(ProofIn, MinIndex),
%		IndexUntouched is MinIndex + I,
%
%		proof(D1, A1L, P1L, ProofIn, ProofBetween1, _),
%		Px := P2 ∪ [[A1L, P1L]], 
%		involve_equivalent_list_pairs([A1, P2], AP, Px, ResultListElements),
%
%		same_elements(A1, A1L), P3 := (P1 ∪ (P2 ∪ P1L)),
%		dict_normalize(ProofBetween1, IndexUntouched, ProofBetween2),

%		proof(D3, LastAssumptions, LastPremisses, ProofBetween2, Proof, _).
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