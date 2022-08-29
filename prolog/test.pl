%  Basic libary to introduce set operators
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

portray(Term) :-
  of_type_A(Term),
  writef("\n", []),
  foreach(member([X1, X2, X3, X4, X5], Term), writef("%p (%p) %p %p %p\n", [X1, X2, X3, X4, X5])).


of_type_A(L) :- 
    forall(member(X, L), (X = [X1 , _, _, _, _], is_list(X1))).

write_type_A(L)