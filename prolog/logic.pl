%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze



% Logical operators
% Connectives
:-op(800, fx, ¬).
:-op(801, xfy, ∧).
:-op(802, xfy, ∨).
:-op(803, xfy, →).
:-op(804, xfy, ↔).
% Derivation symbol
:-op(799, xfy, ⊦).
% Element symbol
:-op(798, xfy, ∈).
:-op(798, xfy, ∉).

binary_connective(X  ∨  Y, X, Y).
binary_connective(X  ∧  Y, X, Y).
binary_connective(X  → Y, X, Y).
binary_connective(X  ↔ Y, X, Y).
binary_derivation(X ⊦ Y, X, Y).

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


% We introduce some derivation symbol which is orientated on intercalation caluli 
% (see "Searching for Proogs (in Sentential Logic)" 
%	from Wilfried Sieg and Richard Scheines)

% Definition of element
X ∈ M :- member(X, M).
X ∉ M :- not(member(X, M)).

% Definition of derivation
% We define some derivation as the same as the intercalation derivation 
Tail ⊦ Head :-
	Tail = (Assumptions, Premisses),
	formula(Head),
	forall(member(X,Assumptions), formula(X)),
	forall(member(X,Premisses), formula(X)).

% Rules of simplification

% Rules from the proposed theorem to towards the hypotheses (bottom-up rules)

% Same as
% A;P?L∧R → A;P?L and A;P?R   
%    with
% AndI = [L ∧ R]  
↑∧(Origin, NextStep, AndI) :-
	Origin = ((A, P) ⊦ (L ∧ R)), 
	NextStep = ((A, P) ⊦ L) ∧ ((A, P) ⊦ R),
	AndI = [L ∧ R].

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
↑∨(Origin, NextStep, ImpI) :-
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

% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A,R;P?C and A;P?L    
%    with
% ImpE = [L → R]  
↓→(Origin, NextStep, ImpE) :-
	Origin = ((A, P1) ⊦ C), 
	NextStep = (((A, P2) ⊦ C) ∧ ((A, P1) ⊦ R)),
	union(A, P1, U), ((L → R) ∈ U), R ∉ U,
	append(P1, [R], P2),
	ImpE = [L → R].

unordered_subset(SubSet, Set):-
  length(LSet, Set),
  between(0,LSubSet, LSet),
  length(LSubSet, NSubSet),
  permutation(NSubSet, SubSet),
  subset(NSubSet, Set).


% Checks, if Weaker_Derivation has more assumptions
% but same conclusion as Derivation. 
% Further on, we say that Weaker_Derivation is weaker then Derivation.
derivation_is_weaker(Weaker_Derivation, Derivation) :-
	binary_derivation(Weaker_Derivation, A0, C0),
	binary_derivation(Derivation, A1, C1),
	subset(A1, A0),
	(((nonvar(C0) -> (C1 = C0)); (C0 = C1))).

% Filters all Theorems X for which Derivation is a weaker Derivation than X 
% and stores them in Useable_Theorems. 
usable_theorems(Derivation, Theorems, Useable_Theorems) :-
	findall(X, 
		(member(X, Theorems), 
		 derivation_is_weaker(Derivation, X)), 
		                             Useable_Theorems).

% Same as usable_theorems. The "Theorems" consist of 
% pairs of an theorem name (Key) and 
% the derivation represented by theorem (Value).
usable_theorems_pairs(Derivation, Theorems, Useable_Theorems) :-
	pairs_values(Theorems, Theorem_Values),
	usable_theorems(Derivation, Theorem_Values, Useable_Theorem_Values),
	pairs_values(Useable_Theorems, Useable_Theorem_Values),
	subset(Useable_Theorems, Theorems).

% Same as usable_theorems_pairs. The theorems consist of an dictionary 
% instead of pairs.
usable_theorems_dict(Derivation, Theorems, Useable_Theorems) :-
	dict_pairs(Theorems, _, Theorems_Pairs),
	usable_theorems_pairs(Derivation, Theorems_Pairs, Useable_Theorems_Pairs),
	dict_pairs(Useable_Theorems, useable_theorems, Useable_Theorems_Pairs).


% Example calls of usable_theorems
% usable_theorems([p,q]⊦p, [[A]⊦A,[A∧B]⊦A], Z).
% usable_theorems_dict([p,q]⊦p, theorems{'d1':[A]⊦A,'d2':[A∧B]⊦A}, Z).
% usable_theorems_pairs([p,q]⊦p, [d1-([A]⊦A), d2-([A∧B]⊦A)], Z).


