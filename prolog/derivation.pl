%  Basic libary to define some derivation syntax
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(propositions, [
    (⊢)/2, op(799, xfy, ⊢),
	binary_derivation/3,
	derivation/1,
	find_derivations/2,					% +LIn, -LOut
	unzip/4,							% +Derivation, -Assumptions, -Premisses, -Conclusion
	isvalid/1,							% +Derivation
	iscontradiction/2,					% +Derivation, -Contradiction
	remove_from_derivation/3,			% +ToRemove, +DerivationIn, -DerivationOut
	replace_derivation_by_inv/3,
	subformulas/3,						%+Derivation, -Subformulas, +Options in ["Assumptions", "Premisses", "Conclusion"]
	has_subformula/3					%+Derivation, +Subformula , +Options in ["Assumptions", "Premisses", "Conclusion"]
]).

:-use_module(invariant).

:-use_module(proposition).
:-use_module(set).



% Logical operators
:-op(799, xfy, ⊢).


% We introduce some derivation symbol which is orientated on intercalation caluli 
% (see "Searching for Proogs (in Sentential Logic)" 
%	from Wilfried Sieg and Richard Scheines)

% Definition of derivation
% We define some derivation as the same as the intercalation derivation 

binary_derivation(X ⊢ Y, X, Y).
Tail ⊢ Head :-
	Tail = (Assumptions, Premisses),
	formula(Head),
	forall(member(X,Assumptions), formula(X)),
	forall(member(X,Premisses), formula(X)).

derivation(X) :- X = (_ ⊢ _).
derivation(X) :- binary_connective(X, A, B), derivation(A), derivation(B).

% removes all elements from LIn, which are not derivations
find_derivations(LIn, LOut) :-
	findall(X, (X ∈ LIn, derivation(X)), LOut).


% extracts Assumptions, Premisses and Conclusion from derivation
unzip(Derivation, Assumptions, Premisses, Conclusion) :-
	Derivation = ((Assumptions, Premisses) ⊢ Conclusion).

% checks if a Derivation is valid without some use of proof steps
isvalid(((A, P) ⊢ C)) :-
	AP := A ∪ P,
	C ∈ AP.

% Checks if their is some contradiction inside of the derivation ((A, P) ⊢ C).
iscontradiction(((A, P) ⊢ _), X) :-
	AP:= A ∪ P, 
	X ∈ AP, ¬(X) ∈ AP. 

% Removes ToRemove from DerivationIn assumptions and premisses and 
remove_from_derivation(ToRemove, DerivationIn, DerivationOut) :-
	DerivationIn = ((A, P) ⊢ C), 
	DerivationOut = ((AO, PO) ⊢ C),
	subtract(A, [ToRemove], AO), subtract(P, [ToRemove], PO).

% Appends Inv at occurences of ToReplace from DerivationIn and sets it in DerivationOut. 
replace_derivation_by_inv(ToReplace, DerivationIn, DerivationOut) :-
	DerivationIn = ((A, P) ⊢ C), 
	DerivationOut = ((AO, PO) ⊢ C),

	replace_by_inv(A, [ToReplace], AO, temp),
	replace_by_inv(P, [ToReplace], PO, temp).

% subformulas/3: Find the subformulas of a sequent (A, P) ⊢ C, based on the given Options.
subformulas((A, P) ⊢ C, Subformulas, Options) :-
    find_subformulas(A, P, C, Options, SubformulasList),
    flatten(SubformulasList, Subformulas).

% Helper predicate to find the subformulas based on the Options.
find_subformulas(A, P, C, Options, SubformulasList) :-
    (member("Assumptions", Options) ->
        maplist(subformulas, A, SubformulasA);
        SubformulasA = []
    ),
    (member("Premisses", Options) ->
        maplist(subformulas, P, SubformulasP);
        SubformulasP = []
    ),
    (member("Conclusion", Options) ->
        subformulas(C, SubformulasC);
        SubformulasC = []
    ),
    append([SubformulasA, SubformulasP, [SubformulasC]], SubformulasList).

% has_subformula/3: Check if a sequent (A, P) ⊢ C contains a specific Subformula based on the given Options.
has_subformula((A, P) ⊢ C, Subformula, Options) :-
    % Retrieve the subformulas based on the Options.
    subformulas((A, P) ⊢ C, Subformulas, Options),
    % Check if Subformula is a member of Subformulas.
    member(Subformula, Subformulas).