
%u(X,Y,Z) :- ground(X), ground(Y), union(X,Y,Z).

f(X,Y,Z) :-
    ( var(X) ; var(Y) ),
    assert(u(X,Y,Z)),
    union(X,Y,Z).
f(X,Y,Z) :-
    ground(X), ground(Y),
    union(X,Y,Z).