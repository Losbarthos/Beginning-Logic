%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(list_helper, [
							integer_list/1,
							after_and_before/4,
				   		insert_front_of/4,
				   		insert_after/4,
				   		split_list_at_nth1/4,
				   		without_last/2,
				   		sort_union/3,
				   		range/3,
				   		subs/4,
				   		split_list/4,
				   		cond1/1
				   		]).


integer_list([]) :- !.
integer_list(L) :-
    L = [X | LB],
    integer(X),
    integer_list(LB).

without_last([_], []).
without_last([X|Xs], [X|WithoutLast]) :- 
    without_last(Xs, WithoutLast).

% Rule that decomposes a list and prints elements before and after some specific element.
after_and_before(Element, List, Before, After):-
  append(Before, [Element|After], List).

% inserts RightFrontBorder in front of occurence of First
insert_front_of(ListIn, RightFrontBorder, First, NewList) :-
	after_and_before(First, ListIn, ListBefore, ListAfter),
	append(RightFrontBorder, [First], Replace),
	append(ListBefore, Replace, NewListBefore),
	append(NewListBefore, ListAfter, NewList).

% inserts LeftFrontBorder after occurence of First
insert_after(ListIn, LeftFrontBorder, First, NewList) :-
	after_and_before(First, ListIn, ListBefore, ListAfter),
	append(ListBefore, [First], NewListBefore),
	append(NewListBefore, LeftFrontBorder, ListAfterInsert),
	append(ListAfterInsert, ListAfter, NewList).

split_list_at_nth1(Nth, Long, Start, End) :-
    length(Start, Nth),
    append(Start, End, Long).

% Gets the set union of elements. The result set is the sorted list of that elements
sort_union(P1, P2, U) :-
	union(P1, P2, U0),
	sort(U0, U).

% range(-List, +A, +B), returns List between two numbers A and B
range([],A,B):-
    A > B.
range([A|T],A,B):-
    A =< B,
    A1 is A + 1,
    range(T,A1,B).


% subs(+X,+Y,+Xs,-Ys) is true if the list Ys is 
% the result of substituting Y for all 
% occurrences of X in the list Xs.
subs(_, _, [], []).
subs(X, Y, [H1|T1], [H2|T2]) :-
    (H1 == X ->
        H2 = Y
    ; is_list(H1) ->
        subs(X, Y, H1, H2),
        subs(X, Y, T1, T2)
    ;
        H1 = H2,
        subs(X, Y, T1, T2)
    ).


% This Prolog predicate splits a list L into two lists P and [H|T]. 
% H is the first element of L which satisfies the predicate Cond. 
% P contains all elements in List before H. 
% P does not contain any element satisfying Cond. 
% T contains all elements which follow H in L.
split_list(Cond, L, P, [H|T]) :-
    split_list_(L, Cond, P, [H|T]).
split_list(_, L, L, []).

split_list_([H|T], Cond, P, [H|R]) :-
    call(Cond, H), split_list_(T, Cond, P, R), !.
split_list_([H|T], Cond, [H|P], R) :-
    split_list_(T, Cond, P, R).
split_list_([], _, [], []).

cond1(Element) :- flatten(Element, F), member(X, F), var(X).