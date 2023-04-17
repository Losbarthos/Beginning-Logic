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
				   		list_without_variables/1,
				   		find_first/3,
				   		create_vector/3,
				   		get_atom_list_with_prefix_between/4,
                        replace/4
				   		]).

:- use_module(library(clpfd)).


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

list_without_variables([]).
list_without_variables([H|T]) :-
    nonvar(H),
    list_without_variables(T).


% This function takes a condition C and a list [X|Xs] as input and returns the
% first element in the list that satisfies the condition. If no such element is
% found, it returns false.

% If the condition is true for the head element of the list, then that element
% is the first one that satisfies the condition, so we return it.
find_first(C, [X|_], X) :-
    call(C, X).

% If the condition is not true for the head element of the list, then we
% recursively search for the first element that satisfies the condition in the
% tail of the list.
find_first(C, [_|Xs], Y) :-
    find_first(C, Xs, Y).

% Define a predicate "create_vector" with three arguments:
% the element to be inserted into the vector, the length of the vector, and the vector itself
create_vector(_, 0, []).
create_vector(Elem, Len, [Elem|Vec]) :-
    Len > 0,
    Len1 is Len - 1,
    create_vector(Elem, Len1, Vec).

% Define a predicate "make_vector" with two arguments:
% the element to be inserted into the vector, and the length of the vector
% It creates the vector by calling "create_vector" with the appropriate arguments
make_vector(Elem, Len, Vec) :-
    create_vector(Elem, Len, Vec).


% Generates a list of atoms with a given prefix and numeric suffixes between two given bounds.
% @param Prefix A prefix that represents the beginning of the generated atoms.
% @param From The lower bound of the numeric suffixes.
% @param To The upper bound of the numeric suffixes.
% @param Atoms The generated list of atoms.
get_atom_list_with_prefix_between(Prefix, From, To, Atoms) :-
    % Use findall/3 to generate a list of atoms.
    findall(Atom, 
            % Use between/3 to iterate over all numeric suffixes between the given bounds.
            (between(From, To, N), 
             % Use atomic_list_concat/2 to generate the atom from the prefix and current suffix.
             atomic_list_concat([Prefix, N], Atom)), 
            % The list of generated atoms.
            Atoms).

% Define the replace/4 predicate that replaces the first occurrence of X with Y in a list
replace(_, _, [], []).
replace(O, R, [O|T], [R|T2]) :- replace(O, R, T, T2).
replace(O, R, [H|T], [H|T2]) :- H \= O, replace(O, R, T, T2).