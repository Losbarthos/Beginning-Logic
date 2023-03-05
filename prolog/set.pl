%  Basic libary to introduce set operators
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(set, [
    (:=)/2, op(699, xfx, :=),
    (∈)/2,  op(599, xfy, ∈),
	(∉)/2,  op(599, xfy, ∉),
	op(598, xfy, ∪),
	op(597, xfy, ∩),
	op(596, xfy, \\),
	set_evaluate/2,
	is_subset/2,
	set_union/3
]).

:- use_module(library(clpfd)).
:-use_module(list_helper).

%:-op(699, xfx, :=).

% Operators to use for sets
%:-op(599, xfy, ∈).
%:-op(599, xfy, ∉).
%:-op(598, xfy, ∪).
%:-op(597, xfy, ∩).



% Definition of element
X ∈ M :- member(X, M).
X ∉ M :- not(member(X, M)).

union_((A ∪ B), C, D) :- union_(A, B, X), union_(X, C, D).
union_(A, (B ∪ C), D) :- union_((A ∪ B), C, D).
union_(A, B, C) :- is_list(A), is_list(B), union(A, B, C).

intersection_((A ∪ B), C, D) :- intersection_(A, B, X), intersection_(X, C, D).
intersection_(A, (B ∪ C), D) :- intersection_((A ∪ B), C, D).
intersection_(A, B, C) :- intersection(A, B, C).

C := (A ∪ B) :- union_(A, B, C).
C := (A ∩ B) :- intersection_(A, B, C).

set_evaluate(A, A) :- ground(A), is_list(A), !.
set_evaluate(A \\ B, E) :- ground(A \\ B), set_evaluate(A, E1), set_evaluate(B, E2), subtract(E1, E2, E), !.
set_evaluate(A ∩ B, E) :- ground(A ∩ B), set_evaluate(A, E1), set_evaluate(B, E2), intersection(E1, E2, E), !.
set_evaluate(A ∪ B, E) :- ground(A ∪ B), set_evaluate(A, E1), set_evaluate(B, E2), union(E1, E2, E), !.




% The predicate is_subset/2 checks whether list A is a subset of list B.
is_subset([], _). % An empty list is always a subset of any other list.
is_subset([X|Xs], B) :- % A non-empty list A is a subset of B if:
    select_ordered(X, B, Bs), % - Its first element X is in B, and
    is_subset(Xs, Bs). % - Its tail Xs is also a subset of B.
    
select_ordered(X, [X|Xs], Xs). % Selects the first occurrence of X in a list, preserving the order of the elements.
select_ordered(X, [_|Xs], Ys) :- % If X is not the first element of the list, recursively search for it in the rest of the list.
    select_ordered(X, Xs, Ys).



set_union(A, B, C) :-
    ( var(A) ; var(B) ) ->
        ( var(A), var(B) -> fdset(C, Set), set_union_vars(Set, [], [], A, B)
        ; var(A) -> set_difference_vars(B, C, A)
        ; set_difference_vars(A, C, B)
        )
    ; list_union(A, B, Union),
      list_to_fdset(Union, UnionSet),
      fdset_to_list(UnionSet, C),
      list_difference(Union, C, Diff),
      all_distinct(Diff).

set_union_vars(Set, A0, B0, A, B) :-
    ( fdset_min(Set, Min) ->
        fdset_delete(Set, Min, Rest),
        ( var(A) -> set_union_vars(Rest, [Min|A0], B0, A, B)
        ; var(B) -> set_union_vars(Rest, A0, [Min|B0], A, B)
        )
    ; reverse(A0, A),
      reverse(B0, B)
    ).

set_difference_vars(Src, Excl, Diff) :-
    list_to_fdset(Src, SrcSet),
    list_to_fdset(Excl, ExclSet),
    fdset_difference(SrcSet, ExclSet, DiffSet),
    fdset_to_list(DiffSet, Diff).

list_union([], B, B).
list_union([X|Xs], B, Union) :-
    member(X, B),
    !,
    list_union(Xs, B, Union).
list_union([X|Xs], B, [X|Union]) :-
    list_union(Xs, B, Union).

list_difference([], _, []).
list_difference([X|Xs], Excl, Diff) :-
    member(X, Excl),
    !,
    list_difference(Xs, Excl, Diff).
list_difference([X|Xs], Excl, [X|Diff]) :-
    list_difference(Xs, Excl, Diff).