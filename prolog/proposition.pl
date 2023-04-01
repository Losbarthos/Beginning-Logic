%  Basic libary to introduce propositions
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(proposition, [
    op(800, fx, ¬),
    op(801, xfy, ∧),
	op(802, xfy, ∨),
	op(803, xfy, →),
	op(804, xfy, ↔),
	binary_connective/3,
	negation/2,
	formula/1,
	variable/1,
	disjunction_list/2, 				% +List, -Disjunction
	conjunction_list/2, 				% +List, -Conjunction
	subformulas/2,						% +Formula, -Subformulas
	⊥ /1,
	set_contradiction/1,
	is_contradiction/1,
	contradictions/2,
	derivation_route/2,					% +From, +To
	has_cases/2,
	has_contradictions/1,
	contains_negation/4,
	get_np/2
]).

:-use_module(my_term).
:-use_module(set).

% Logical operators
% Connectives.

:-op(800, fx, ¬).
:-op(801, xfy, ∧).
:-op(802, xfy, ∨).
:-op(803, xfy, →).
:-op(804, xfy, ↔).

binary_connective(X  ∨  Y, X, Y).
binary_connective(X  ∧  Y, X, Y).
binary_connective(X  → Y, X, Y).
binary_connective(X  ↔ Y, X, Y).
negation(¬(X), X).

% Definition of formulas used in propositional logic
formula(X) :-
    variable(X).
formula(Binary) :-
    binary_connective(Binary, X, Y),
    formula(X),
    formula(Y).
formula(¬ X) :-
    formula(X).

% define contradiction symbol
⊥(0).
⊥(N) :- ⊥(M), N is M + 1.

% Used as atoms or individual symbols
variable(p).
variable(q).
variable(r).
variable(⊥(N)) :- ⊥(N).

% Converts a list l1,...,ln into (l1 ∨ (l2 ∨ ( ... ∨ ln)...)
disjunction_list(List, Disjunction) :- 
	List = [Head | Tail], 
	disjunction_list(Tail, Sub),
	Disjunction = (Head ∨ Sub).
disjunction_list(List, Disjunction) :-
	List = [X], length(List, 1), Disjunction = X.

% Converts a list l1,...,ln into (l1 ∧ (l2 ∧ ( ... ∧ ln)...)
conjunction_list(List, Disjunction) :- 
	List = [Head | Tail], 
	disjunction_list(Tail, Sub),
	Disjunction = (Head ∧ Sub).
conjunction_list(List, Disjunction) :-
	List = [X], length(List, 1), Disjunction = X.

% Definition of subformula
subformulas(Formula, Subformulas) :- 
			formula(Formula),
			flatten_terms(Formula, Subformulas).

get_next_element(N, N) :- not(⊥(N)), assert(⊥(N)), !.
get_next_element(N, M) :- ⊥(N), O is N + 1, get_next_element(O, M).

set_contradiction(N) :- get_next_element(0, N).

% Contradiction rules
is_contradiction(A):- A = (X ∧ ¬X).%, formula(X).
is_contradiction(A):- A = (¬X ∧ X).%, formula(X).
is_contradiction(A):- A = ⊥(_).

% contradictions(+B, -C)
% Gets all possible contradictions withhin negation elemination and introduction

% The set of contradictions of A ∧ B, A ∨ B, A → C and A ↔ B is the union of the set of contradictions of A
% with the set of contradictions of B
contradictions(B, C) :-
	binary_connective(B, X, Y), 
	contradictions(X, C1), 
	contradictions(Y, C2), 
	C := C1 ∪ C2.
% The set of contradictions of a negation ¬ A only consists of ¬ A itself.
contradictions(B, C) :-
	B = ¬(A), 
	C = [A].
% The set of contradictions of some variable is empty.
contradictions(B, C) :-
	subformulas(B, S),
	findall(X, (X ∈ S, X = ¬(_)), Neg),
	length(Neg, 0), 
	C = [].
% Find all contradictions for some list of propositions.
contradictions(B, C) :-
	findall(X, (Y ∈ B, not(is_list(Y)), contradictions(Y, X)), SC),
	append(SC, C0), sort(C0, C).

% checks, if it is some derivation route from "From" to "To"
derivation_route(From, To) :-
	From = To.
derivation_route(From, To) :-
	binary_connective(To, X, _), derivation_route(From, X).
derivation_route(From, To) :-
	binary_connective(To, _, Y), derivation_route(From, Y).

% Checks whether a case C occurs as disjunct in the disjunction d1 ∨ d2 ∨ ... ∨ dn 
is_case_of(C, D) :-
	C = D.
is_case_of(C, D) :-
	D = (D1 ∨ _),
	is_case_of(C, D1).
is_case_of(C, D) :-
	D = (_ ∨ D2),
	is_case_of(C, D2).

% Checks if the set S has at least one X with is_case_of(X, D)
has_cases(S, D) :-
	member(X, S), is_case_of(X, D).

% checks, if the set S has contradictions. 
has_contradictions(S) :- A ∈ S, ¬(A) ∈ S.

contains_negation(L, C, N, R) :-
    member(N, L),
    (   ¬(N) = C, R = "¬I"
    ;   ¬(C) = N, R = "¬E"
    ).	

% This function takes a proposition P as input and determines the value of the
% second parameter NP based on the form of P.

% If P is of the form ¬(P0), then NP is set to P0.
get_np(P, NP) :- 
    P =.. [¬, P0], 
    NP = P0.
get_np(P, NP) :- 
    P =.. [P0], 
    P0 \= ¬(_), 
    NP =.. [¬, P].