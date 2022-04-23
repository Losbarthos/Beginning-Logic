invariant_2(X, F, Y) :-
	Y = F(F(X)).
invariant_2(X, F, Y) :-
	Y = F(F(Z)), invariant_2(X, F, Z).

reduce_2n_invariant(LIn, F, LOut) :-
	findall(X, (member(X, LIn), forall(Y, (member(Y, LIn), not(invariant(Y,F,X))))), LOut).
