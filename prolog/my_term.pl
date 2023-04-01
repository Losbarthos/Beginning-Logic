%  Basic libary to trace something into log proof_trace.txt
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2023, Martin Kunze

:- module(my_term, [
                     flatten_terms/2,
                     contains_term/2
]).

% flatten_terms/2: Flatten a given Term into a list of its sub-terms (FlatList).
flatten_terms(Term, FlatList) :-
    % Decompose the Term into its main functor and its arguments (Args).
    Term =.. [_ | Args],
    % Recursively flatten each argument in Args, and collect the results in FlatArgs.
    maplist(flatten_terms, Args, FlatArgs),
    % Append the FlatArgs with the original Term to form NoFlatList.
    append(FlatArgs, [Term], NoFlatList),
    % Flatten NoFlatList and remove duplicates to obtain the final FlatList.
    flatten(NoFlatList, UFlatList), sort(UFlatList, FlatList).

% contains_term/2: Check if a given Term contains a specific SubTerm.
contains_term(Term, SubTerm) :-
    % Flatten the Term into a list of its sub-terms (FlatList).
    flatten_terms(Term, FlatList),
    % If SubTerm is a member of FlatList, then Term contains SubTerm.
    member(SubTerm, FlatList), !.