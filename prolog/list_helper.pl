%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(list_helper, [
						after_and_before/4,
				   		insert_front_of/4,
				   		insert_after/4
				   		]).
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