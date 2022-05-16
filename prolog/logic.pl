%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

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
:-op(799, xfy, ⊦).


% Operators to use for sets
:-op(599, xfy, ∈).
:-op(599, xfy, ∉).
:-op(598, xfy, ∪).
:-op(597, xfy, ∩).

binary_connective(X  ∨  Y, X, Y).
binary_connective(X  ∧  Y, X, Y).
binary_connective(X  → Y, X, Y).
binary_connective(X  ↔ Y, X, Y).
binary_derivation(X ⊦ Y, X, Y).
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
C := (A ∪ B) :- union(A, B, C).
C := (A ∩ B) :- intersection(A, B, C).

% Definition of derivation
% We define some derivation as the same as the intercalation derivation 
Tail ⊦ Head :-
	Tail = (Assumptions, Premisses),
	formula(Head),
	forall(member(X,Assumptions), formula(X)),
	forall(member(X,Premisses), formula(X)).

derivation(X) :- X = (_ ⊦ _).
derivation(X) :- binary_connective(X, A, B), derivation(A), derivation(B).

% extracts Assumptions, Premisses and Conclusion from derivation
unzip(Derivation, Assumptions, Premisses, Conclusion) :-
	Derivation = ((Assumptions, Premisses) ⊦ Conclusion).

% checks if a Derivation is valid without some use of proof steps
isvalid(((A, P) ⊦ C)) :-
	AP := A ∪ P,
	C ∈ AP.

% Contradiction rules
⊥(A):- A = (X ∧ ¬X), formula(X).
⊥(A):- A = (¬X ∧ X), formula(X).

% Rules of simplification (need improvement)

% Same as
% A;P?L∨R → A;P?L or A;P?R   
%    with
% OrI = [L ∧ R]  
↑∨(Origin, NextStep, OrI) :-
	Origin = ((A, P) ⊦ (L ∨ R)), 
	NextStep = ((A, P) ⊦ L) ∨ ((A, P) ⊦ R),
	OrI = [L ∨ R].

% Same as
% [A;P?L→R] → A,L;P?R   
%    with
% ImpI = [L → R]  
↑→(Origin, NextStep, ImpI) :-
	Origin = ((A1, P) ⊦ (L → R)),
	NextStep = ((A2, P) ⊦ R),
	append(A1, [L], A2),
	ImpI = [L → R].

%
% Rules from the assumptions towards the prposed theorem (top-down rules)
%


% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), L or R ∉ (A ∪ P)] → A;P,L or R?C   
%    with
% AndE = [L ∧ R, L or R]  
↓∧(Origin, NextStep, AndE) :- 
	(Origin = ((A, P1) ⊦ C), NextStep = ((A, P2) ⊦ C),
		union(A, P1, U), ((L ∧ R) ∈ U),
	(L ∉ U), append(P1, [L], P2), AndE = [L ∧ R, L]);
	(Origin = ((A, P1) ⊦ C), NextStep = ((A, P2) ⊦ C),
		union(A, P1, U), ((L ∧ R) ∈ U),
	(R ∉ U), append(P1, [R], P2), AndE = [L ∧ R, R]).

andE_s(Origin, NextStep, AndE) :-
	↓∧(Origin_old, NextStep_old, AndE_old),
	term_to_atom(Origin_old, Origin), term_to_atom(NextStep_old, NextStep), term_to_atom(AndE_old, AndE). 


% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P), L, R ∉ (A ∪ P)] → A,L;P?C and A,R;P?C    
%    with
% OrE = [L ∨ R]  
↓∨(Origin, NextStep, OrE) :-
	Origin = ((A1, P) ⊦ C), 
	NextStep = (((A2, P) ⊦ C) ∧ ((A3, P) ⊦ C)),
	union(A1, P, U), ((L ∨ R) ∈ U), L ∉ U, R ∉ U,
	append(A1, [L], A2), append(A1, [R], A3),
	OrE = [L ∨ R].


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
	findall(X, (Y ∈ B, contradictions(Y, X)), SC),
	append(SC, C).

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

%
% Derivations which can used in the proof.
%

% Same as
% A;P?L∧R → A;P?L and A;P?R   
% RuleName: ∧I
rule(Origin, NextStep, DictIn, DictOut) :-
	Origin = ((A, P) ⊦ (L ∧ R)), 
	NextStep = (((A, P) ⊦ L) ∧ ((A, P) ⊦ R)),

	%%
	% Filling DictOut
	%%
	Assumptions = A,
	PremissesOrigin = [L, R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L ∧ R],
	Rule = "∧I",


	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DictIn, DictOut).

%	dict_min_index(DictIn, CIndexIn), plus(CIndexOut, 1, CIndexIn),
%	term_string(edge([L, L ∧ R]), Atom1), term_string(edge([R, L ∧ R]), Atom2),
%	sort(A, ASort), term_string(assumptions(ASort), Atom3),
%	term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
%	DictOut = DictIn.put([CIndexOut = [Atom3, Atom1, Atom2, "rule([∧I])", AtomOriginDerivation, AtomNextDerivation]]).

% Same as
% [A;P?L→R] L ∈ (A ∪ P) → A;P?R   
%    with
% RuleName: →I
rule(Origin, NextStep, DictIn, DictOut) :-
	Origin = ((A, P) ⊦ (L → R)), 
	union(A, P, U), L ∈ U,
	NextStep = ((A, P) ⊦ R), 

	%%
	% Filling DictOut
	%%
	Assumptions = A,
	PremissesOrigin = [L, R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L → R],
	Rule = "→I",


	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						    Conclusion, Rule, DictIn, DictOut).

	%dict_min_index(DictIn, CIndexIn), plus(CIndexOut, 1, CIndexIn), term_string(edge([L, L → R]), Atom2), term_string(edge([R, L → R]), Atom3),
	%sort(A, ASort), term_string(assumptions(ASort), Atom4), 
	%term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
	%DictOut = DictIn.put([CIndexOut = [Atom4, Atom2, Atom3, "rule([→I])", AtomOriginDerivation, AtomNextDerivation]]).

% Same as
% [A;P?L→R] → A,L;P?R   
%    with
% RuleName: →I
rule(Origin, NextStep, DictIn, DictOut) :-
	Origin = ((A1, P) ⊦ (L → R)),
	union(A1, P, U), L ∉ U, 
	NextStep = ((A2, P) ⊦ R),
	append(A1, [L], A2), 

	%%
	% Filling DictOut
	%%
	Assumptions = A2,
	PremissesOrigin = [R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [L],
	Conclusion = [L → R],
	Rule = "→I",


	dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						    Conclusion, Rule, DictIn, DictOut).

	%dict_min_index(DictIn, CIndexIn), plus(CIndexOut, 1, CIndexIn),
	%dict_max_index(DictIn, AIndexIn), succ(AIndexIn, AIndexOut), 
	%term_string(L, Atom1), term_string(edge([L, L → R]), Atom2), term_string(edge([R, L → R]), Atom3),
	%sort(A2, A2Sort), term_string(assumptions(A2Sort), Atom4), term_string(except([L]), Atom5), 
	%term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
	%DictOut = DictIn.put([AIndexOut = Atom1, CIndexOut = [Atom4, Atom5, Atom2, Atom3, "rule([→I])", AtomOriginDerivation, AtomNextDerivation]]).

% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), L ∉ (A ∪ P)] → A;P,L   
%    with
% RuleName: ∧E
rule(Origin, NextStep, DictIn, DictOut) :- 
	Origin = ((A, P1) ⊦ C), NextStep = ((A, P2) ⊦ C),
	union(A, P1, U), ((L ∧ R) ∈ U),
	(L ∉ U), temp(L ∧ R) ∉ U, temp(L) ∉ U, append(P1, [L], P2),

	%%
	% Filling DictOut
	%%
	Assumptions = A,
	PremissesOrigin = [L ∧ R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [L],
	Rule = "∧E",


	dict_proof_append_last(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DictIn, DictOut).

	%dict_max_index(DictIn, AIndexIn), succ(AIndexIn, AIndexOut),
	%term_string(edge([L ∧ R, L]), Atom1), sort(A, ASort), term_string(assumptions(ASort), Atom2),
	%term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
	%DictOut = DictIn.put([AIndexOut = [Atom2, Atom1, "rule([∧E])", AtomOriginDerivation, AtomNextDerivation]]).

% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;P,R   
%    with
% RuleName: ∧E
rule(Origin, NextStep, DictIn, DictOut) :- 
	Origin = ((A, P1) ⊦ C), NextStep = ((A, P2) ⊦ C),
	union(A, P1, U), ((L ∧ R) ∈ U),
	(R ∉ U), temp(L ∧ R) ∉ U, temp(R) ∉ U, append(P1, [R], P2),

	%%
	% Filling DictOut
	%%
	Assumptions = A,
	PremissesOrigin = [L ∧ R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [R],
	Rule = "∧E",


	dict_proof_append_last(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, DictIn, DictOut).

	%dict_max_index(DictIn, AIndexIn), succ(AIndexIn, AIndexOut),
	%term_string(edge([L ∧ R, R]), Atom1), sort(A, ASort), term_string(assumptions(ASort), Atom2),
	%term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
	%DictOut = DictIn.put([AIndexOut = [Atom2, Atom1, "rule([∧E])", AtomOriginDerivation, AtomNextDerivation]]).

% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L    
% RuleName: →E
rule(Origin, NextStep, DictIn, DictOut) :-
	Origin = ((A1, P1) ⊦ C), 
	NextStep1 = ((A2, P2) ⊦ L),
	

	union(A1, P1, U1), ((L → R) ∈ U1), R ∉ U1, not(C=L), temp(L → R) ∉ U1, temp(R) ∉ U1,
	delete(A1, (L → R), A2), delete(P1, (L → R), P12), append(P12, [temp(L → R)], P2),

	dict_min_index(DictIn, IndexUntouched),

	proof(NextStep1, NewAssumptions, NewPremisses, DictIn, ProofRaw),
	no_temp(NewAssumptions, MidAssumptions), no_temp(NewPremisses, MidPremisses),
	union(MidAssumptions, MidPremisses, U2), ((L → R) ∉ U2), R ∉ U2,
	union(A1, MidAssumptions, LastAssumptions), union(P1, MidPremisses, MidLastPremisses),
	append(MidLastPremisses, [R], LastPremisses), 
	NextStep = ((LastAssumptions, LastPremisses) ⊦ C),

	dict_normalize(ProofRaw, IndexUntouched, Proof),


	%%
	% Filling DictOut
	%%
	Assumptions = A1,
	PremissesOrigin = [L, L → R],
	PremissesNoOrigin = [],
	PremissesExcOrigin = [],
	Conclusion = [R],
	Rule = "→E",


	dict_proof_append_last(Assumptions, PremissesOrigin, PremissesNoOrigin, PremissesExcOrigin,
						   Conclusion, Rule, Proof, DictOut).


	%dict_max_index(Proof, AIndexIn), succ(AIndexIn, AIndexOut),
	%term_string(edge([L, R]), Atom1), term_string(edge([L → R, R]), Atom2), 
	%sort(A1, A1Sort), term_string(assumptions(A1Sort), Atom3),
	%term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
	%DictOut = Proof.put([AIndexOut = [Atom3, Atom1, Atom2, "rule([→E])", AtomOriginDerivation, AtomNextDerivation]]).

% Same as
% [A;P?C, (C ∧ ¬C) ∉ A, ¬C ∉ A] → (A,¬C;P?(X1 ∧ ¬X1)) ∨ (A,¬C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,¬C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬E 
% Remark: maybe its better to say ¬Xi ∈ (A ∪ P ∪ {¬C}), but already no counterexample for ¬Xi ∈ (A ∪ P) found.
c_rule(Origin, NextStep, DictIn, DictOut, CAssumption, ContraPremiss) :-
	Origin = ((A1, P) ⊦ C), CAssumption = ¬(C), ContraPremiss = C,
	not(⊥(C)), union(A1, P, U), (¬(C) ∉ U), (temp(¬(C)) ∉ U), append(A1, [¬(C)], A2), not(anymember_invariant_2n(U, ¬(C), ¬)),
	union(A2, P, U2), contradictions(U2, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P) ⊦ (Y ∧ ¬(Y)))), NextStepList),
	disjunction_list(NextStepList, NextStep),

%	dict_min_index(DictIn, CIndexIn), plus(CIndexOut, 1, CIndexIn),
%	dict_max_index(DictIn, AIndexIn), succ(AIndexIn, AIndexOut), 
	findall(X, (member(Y, Contra), 
				%%
				% Filling DictOut
				%%
				Assumptions = A2,
				PremissesOrigin = [Y ∧ ¬(Y)],
				PremissesNoOrigin = [],
				PremissesExcOrigin = [¬(C)],
				Conclusion = [C],
				Rule = "¬E",

				dict_proof_append_assumption(¬(C), DictIn, XBuffer),
				dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, 
										PremissesExcOrigin,
										Conclusion, Rule, XBuffer, X)),


%				sort(A2, A2Sort),
%				term_string(¬(C), Atom1), term_string(edge([¬(C), C]), Atom2),
%				term_string(edge([Y ∧ ¬(Y), C]), Atom3), term_string(assumptions(A2Sort), Atom4),
%				term_string(except([¬(C)]), Atom5),
%				term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
%				X = DictIn.put([AIndexOut = Atom1, 
%								CIndexOut = [Atom4, Atom5, Atom2, Atom3, "rule([¬E])", AtomOriginDerivation, AtomNextDerivation]])),
				NegEList),
	disjunction_list(NegEList, DictOut).

% Same as
% [A;P?¬C, (C ∧ ¬C) ∉ A, C ∉ A] → (A,C;P?(X1 ∧ ¬X1)) ∨ (A,C;P?(X2 ∧ ¬X2)) ∨ ... ∨ (A,C;P?(Xn ∧ ¬Xn))    
%    with
% ¬Xi ∈ (A ∪ P)
% RuleName: ¬I 
c_rule(Origin, NextStep, DictIn, DictOut, CAssumption, ContraPremiss) :-
	Origin = ((A1, P) ⊦ ¬(C)), CAssumption = C, ContraPremiss = ¬(C),
	not(⊥(C)), union(A1, P, U), (C ∉ U), temp(C) ∉ U, append(A1, [C], A2), not(anymember_invariant_2n(U, C, ¬)),
	union(A2, P, U2), contradictions(U2, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P) ⊦ (Y ∧ ¬(Y)))), NextStepList),
	disjunction_list(NextStepList, NextStep),

	%dict_min_index(DictIn, CIndexIn), plus(CIndexOut, 1, CIndexIn),
	%dict_max_index(DictIn, AIndexIn), succ(AIndexIn, AIndexOut), 
	
	findall(X, (member(Y, Contra), 
				%%
				% Filling DictOut
				%%
				Assumptions = A2,
				PremissesOrigin = [Y ∧ ¬(Y)],
				PremissesNoOrigin = [],
				PremissesExcOrigin = [C],
				Conclusion = [¬(C)],
				Rule = "¬I",

				dict_proof_append_assumption(C, DictIn, XBuffer),
				dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, 
										PremissesExcOrigin,
										Conclusion, Rule, XBuffer, X)),


				%sort(A2, A2Sort),
				%term_string(C, Atom1), term_string(edge([C, ¬(C)]), Atom2),
				%term_string(edge([Y ∧ ¬(Y), ¬(C)]), Atom3), term_string(assumptions(A2Sort), Atom4),
				%term_string(except([C]), Atom5),
				%term_string(Origin, AtomOriginDerivation), term_string(NextStep, AtomNextDerivation),
				%X = DictIn.put([AIndexOut = Atom1, 
				%				CIndexOut = [Atom4, Atom5, Atom2, Atom3, "rule([¬I])", AtomOriginDerivation, AtomNextDerivation]])),
			NegIList),
	disjunction_list(NegIList, DictOut).

%
% Proofs some Derivation
%

proof(Derivation, LastAssumptions, LastPremisses, Proof, Proof) :- 	
		Derivation = ((LastAssumptions, LastPremisses) ⊦ _),
		isvalid(Derivation),!.

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof) 	:- 	
		Derivation = (D1 ∧ D2),
		D1 = ((A1, P1) ⊦ C), 
		union(A1, A2, A), union(P1, P2, P),
		D = ((A, P) ⊦ C),
		proof(D2, A2, P2, ProofIn, ProofBetween),
		proof(D, LastAssumptions, LastPremisses, ProofBetween, Proof),!.

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof) :- 	
		%not(isvalid(Derivation)),
		rule(Derivation, NextStep, ProofIn, ProofOut), 
		proof(NextStep, LastAssumptions, LastPremisses, ProofOut, Proof),!.

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof) :- 	
		%not(isvalid(Derivation)),
		%not(rule(Derivation, NextStep, ProofIn, ProofOut)),
		c_rule(Derivation, NextStep, ProofIn, ProofOut, CAssumption, Assumption), 
		proof(NextStep, MidAssumptions, MidPremisses, ProofOut, Proof),
		delete(MidAssumptions, CAssumption, LastAssumptions),
		append(MidPremisses, [Assumption], LastPremisses).

proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof) :- 
		Derivation = (D1 ∨ _),
		ProofIn = (Proof1 ∨ _),
		proof(D1, LastAssumptions, LastPremisses, Proof1, Proof).
proof(Derivation, LastAssumptions, LastPremisses, ProofIn, Proof) :- 
		Derivation = (_ ∨ D2),
		ProofIn = (_ ∨ Proof2),
		proof(D2, LastAssumptions, LastPremisses, Proof2, Proof),!.

proof(Derivation, Proof) :- 
	distinct([Proof], (Derivation = ((A, []) ⊦ _),
	findall(X, (member(Y, A), term_string(Y,X)), AA),
	list_to_dict(AA, proof, Assumptions),
	proof(Derivation, _, _, Assumptions, ProofRaw),
	dict_normalize(ProofRaw, 1, Proof))).


% Examples
% ?- proof((([¬(q),p→q], []) ⊦ ¬(p)), P).
%


proof_py(Derivation, Proof) :-
	proof(Derivation, Proof1), 
	term_to_atom(Proof1, Proof).

proof_t(Derivation, Proof) :-
	proof(Derivation, Proof1),
	Proof = Proof1._.