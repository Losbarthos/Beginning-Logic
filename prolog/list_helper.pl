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
				   		without_last/2
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