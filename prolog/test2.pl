%:- module(test2,[test2/1]).

:-use_module(test).

test2(A) :- A := [1,2] ∪ [3,4].