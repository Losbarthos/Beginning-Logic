:-op(800, fx, ~).
:-op(801, xfy, ∧).
:-op(802, xfy, ∨).
:-op(803, xfy, →).
:-op(804, xfy, ↔).
:-op(799, xfy, ⊦).


binary_connective(X  ∨  Y, X, Y).
binary_connective(X  ∧  Y, X, Y).
binary_connective(X  → Y, X, Y).
binary_connective(X  ⟷ Y, X, Y).
binary_derivation(X ⊦ Y, X, Y).


formula(X) :-
    variable(X).
formula(Binary) :-
    binary_x_y(Binary, X, Y),
    formula(X),
    formula(Y).
formula(~ X) :-
    formula(X).

variable(p).
variable(q).

% Definition of derivation
Assumptions ⊦ Conclusion :- 
	forall(member(X,Assumptions), formula(X)), formula(Conclusion).

% Checks, if Weaker_Derivation has more assumptions
% but same conclusion as Derivation. 
% Further on, we say that Weaker_Derivation is weaker then Derivation.
derivation_is_weaker(Weaker_Derivation, Derivation) :-
	binary_derivation(Weaker_Derivation, A0, C0),
	binary_derivation(Derivation, A1, C1),
	C0 = C1,
	subset(A1, A0).

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