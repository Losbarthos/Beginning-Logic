:-op(800, fx, ~).
:-op(801, xfy, ∧).
:-op(802, xfy, ∨).
:-op(803, xfy, →).
:-op(804, xfy, ⟷).
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

% Checks, if Weaker_Derivation has more assumptions to conclude
% the same conclusion as Derivation. 
% Further on, we say that Weaker_Derivation is weaker then Derivation.
derivation_is_weaker(Weaker_Derivation, Derivation) :-
	binary_derivation(Weaker_Derivation, A0, C0),
	binary_derivation(Derivation, A1, C1),
	C0 = C1,
	subset(A1, A0).

% Filters all Theorems X for which Derivation is a weaker Derivation than X 
% and stores them in Usable_Theorems. 
usable_theorems(Derivation, Theorems, Usable_Theorems) :-
	subset(Usable_Theorems, Theorems),
	forall(member(X, Usable_Theorems), 
				derivation_is_weaker(Derivation, X)).

% usable_theorems([p,q]⊦p,[[A]⊦A,[A∧B]∧A],Z).
