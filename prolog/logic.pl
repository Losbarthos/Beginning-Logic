%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

% Logical operators
% Connectives
:-op(800, fx, ¬).
:-op(801, xfy, ∧).
:-op(802, xfy, ∨).
:-op(803, xfy, →).
:-op(804, xfy, ↔).
% Derivation symbol
:-op(799, xfy, ⊦).
% Element symbol
:-op(798, xfy, ∈).
:-op(798, xfy, ∉).

binary_connective(X  ∨  Y, X, Y).
binary_connective(X  ∧  Y, X, Y).
binary_connective(X  → Y, X, Y).
binary_connective(X  ↔ Y, X, Y).
binary_derivation(X ⊦ Y, X, Y).

% Definition of formulas used in propositional logic
formula(X) :-
    variable(X).
formula(Binary) :-
    binary_connective(Binary, X, Y),
    formula(X),
    formula(Y).
formula(¬ X) :-
    formula(X).

% Used as atoms or individual symbols
variable(p).
variable(q).
variable(r).

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
			variable(Formula), 
			Subformulas = [Formula].
subformulas(Formula, Subformulas) :-
			binary_connective(Formula, X, Y),
			subformulas(X, S1),
			subformulas(Y, S2),
			union(S1, S2, SXY),
			union(SXY,[Formula],Subformulas).

subformulas(Formula, Subformulas) :-
			Formula = ¬(X),
			subformulas(X, S1),
			union(S1, [¬(X)], Subformulas).


% We introduce some derivation symbol which is orientated on intercalation caluli 
% (see "Searching for Proogs (in Sentential Logic)" 
%	from Wilfried Sieg and Richard Scheines)

% Definition of element
X ∈ M :- member(X, M).
X ∉ M :- not(member(X, M)).

% Definition of derivation
% We define some derivation as the same as the intercalation derivation 
Tail ⊦ Head :-
	Tail = (Assumptions, Premisses),
	formula(Head),
	forall(member(X,Assumptions), formula(X)),
	forall(member(X,Premisses), formula(X)).

derivation(X) :- X = (_ ⊦ _).
derivation(X) :- binary_connective(X, A, B), derivation(A), derivation(B).

% extracts Assumptions, Premisses and Conclusion from derivation
unzip(Derivation, Assumptions, Premisses, Conclusion) :-
	Derivation = ((Assumptions, Premisses) ⊦ Conclusion).

% checks if a Derivation is valid without some use of proof steps
isvalid(((Assumptions, Premisses) ⊦ Conclusion)) :-
	union(Assumptions, Premisses, U),
	member(Conclusion, U).



% Rules of simplification

% Rules from the proposed theorem to towards the hypotheses (bottom-up rules)

% Same as
% A;P?L∧R → A;P?L and A;P?R   
%    with
% AndI = [L ∧ R]  
↑∧(Origin, NextStep, AndI) :-
	Origin = ((A, P) ⊦ (L ∧ R)), 
	NextStep = [((A, P) ⊦ L), ((A, P) ⊦ R)],
	AndI = [L ∧ R, L, R].

% Same as
% A;P?L∨R → A;P?L or A;P?R   
%    with
% OrI = [L ∧ R]  
↑∨(Origin, NextStep, OrI) :-
	Origin = ((A, P) ⊦ (L ∨ R)), 
	NextStep = ((A, P) ⊦ L) ∨ ((A, P) ⊦ R),
	OrI = [L ∨ R].

% Same as
% [A;P?L→R] → A,L;P?R   
%    with
% ImpI = [L → R]  
↑→(Origin, NextStep, ImpI) :-
	Origin = ((A1, P) ⊦ (L → R)),
	NextStep = ((A2, P) ⊦ R),
	append(A1, [L], A2),
	ImpI = [L → R].

%
% Rules from the assumptions towards the prposed theorem (top-down rules)
%


% Same as
% [A;P?C, (L ∧ R) ∈ (A ∪ P), L or R ∉ (A ∪ P)] → A;P,L or R?C   
%    with
% AndE = [L ∧ R, L or R]  
↓∧(Origin, NextStep, AndE) :- 
	(Origin = ((A, P1) ⊦ C), NextStep = ((A, P2) ⊦ C),
		union(A, P1, U), ((L ∧ R) ∈ U),
	(L ∉ U), append(P1, [L], P2), AndE = [L ∧ R, L]);
	(Origin = ((A, P1) ⊦ C), NextStep = ((A, P2) ⊦ C),
		union(A, P1, U), ((L ∧ R) ∈ U),
	(R ∉ U), append(P1, [R], P2), AndE = [L ∧ R, R]).

andE_s(Origin, NextStep, AndE) :-
	↓∧(Origin_old, NextStep_old, AndE_old),
	term_to_atom(Origin_old, Origin), term_to_atom(NextStep_old, NextStep), term_to_atom(AndE_old, AndE). 


% Same as
% [A;P?C, (L ∨ R) ∈ (A ∪ P), L, R ∉ (A ∪ P)] → A,L;P?C and A,R;P?C    
%    with
% OrE = [L ∨ R]  
↓∨(Origin, NextStep, OrE) :-
	Origin = ((A1, P) ⊦ C), 
	NextStep = (((A2, P) ⊦ C) ∧ ((A3, P) ⊦ C)),
	union(A1, P, U), ((L ∨ R) ∈ U), L ∉ U, R ∉ U,
	append(A1, [L], A2), append(A1, [R], A3),
	OrE = [L ∨ R].

% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L    
%    with
% ImpE = [L → R]  
↓→(Origin, NextStep, ImpE) :-
	Origin = ((A1, P1) ⊦ C), 
	NextStep = [((A1, P2) ⊦ C), ((A3, P3) ⊦ L)],
	union(A1, P1, U), ((L → R) ∈ U), R ∉ U,
	delete(A1, (L → R), A3), delete(P1, (L → R), P3),
	append(P1, [R], P2),
	ImpE = [R, L → R, L].


% Contradiction rules
⊥(A):- (A = (X ∧ (¬X));A = ((¬X) ∧ X)), formula(X).

% Gets all possible contradictions withhin negation elemination and introduction
contradictions(Base, Contradictions) :-
	findall(X, ((X ∈ Base), variable(X)), Variables),
	findall(X, (¬(X) ∈ Base), Negatable),
	findall(X,
		(((_ → X) ∈ Base), 
		subformulas(X, S), 
		not(subset(S, Base))), Consequences),
	union(Variables, Negatable, S1), 
	union(S1, Consequences, Contradictions).


↓¬¬(Origin, NextStep, NegE) :-
	Origin = ((A1, P) ⊦ C),
	not(⊥(C)), (¬(C) ∉ A1), append(A1, [¬(C)], A2),
	union(A1, P, U), contradictions(U, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P) ⊦ (Y ∧ ¬(Y)))), NextStep),
	findall(X, (member(Y, Contra), X=[C,(Y ∧ ¬(Y)), ¬(C)]), NegE).

↓¬(Origin, NextStep, NegI) :-
	Origin = ((A1, P) ⊦ ¬(C)),
	not(⊥(C)), (C ∉ A1), append(A1, [C], A2),
	union(A1, P, U), contradictions(U, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P) ⊦ (Y ∧ ¬(Y)))), NextStep),
	findall(X, (member(Y, Contra), X=[¬(C),(Y ∧ ¬(Y)), C]), NegI).


% Same as
% A;P?L∧R → A;P?L and A;P?R   
%    with
% AndI = [L ∧ R]  
rule(Origin, NextStep, AndI, N) :-
	Origin = ((A, P) ⊦ (L ∧ R)), 
	NextStep = (((A, P) ⊦ L) ∧ ((A, P) ⊦ R)),
	format(atom(AndI), '"~w": ["~w", "~w", "~w"]', [N, edge(L, L ∧ R), edge(R, L ∧ R), rule('∧I')]).

% Same as
% [A;P?C, (L → R) ∈ (A ∪ P), R ∉ (A ∪ P)] → A;R,P?C and A\(L → R);P\(L → R)?L    
%    with
% ImpE = [L → R]  
rule(Origin, NextStep, ImpE, N) :-
	Origin = ((A1, P1) ⊦ C), 
	NextStep = (((A1, P2) ⊦ C) ∧ ((A3, P3) ⊦ L)),
	union(A1, P1, U), ((L → R) ∈ U), R ∉ U,
	delete(A1, (L → R), A3), delete(P1, (L → R), P3),
	append(P1, [R], P2),
	format(atom(ImpE), '"~w": ["~w", "~w", "~w"]', [N, edge(L, R), edge(L → R, R), rule('→E')]).

rule(Origin, NextStep, NegE, N) :-
	Origin = ((A1, P) ⊦ C),
	not(⊥(C)), (¬(C) ∉ A1), append(A1, [¬(C)], A2),
	union(A1, P, U), contradictions(U, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P) ⊦ (Y ∧ ¬(Y)))), NextStepList),
	disjunction_list(NextStepList, NextStep),
	findall(X, (member(Y, Contra), 
				format(atom(X), '"~w": ["~w", "~w", "~w", "~w"]', 
					   [N, origin_node(¬(C)), edge(¬(C), C), edge(Y ∧ ¬(Y), C), rule('¬E')])),
				NegEList),
	disjunction_list(NegEList, NegE).

rule(Origin, NextStep, NegI, N) :-
	Origin = ((A1, P) ⊦ ¬(C)),
	not(⊥(C)), (C ∉ A1), append(A1, [C], A2),
	union(A1, P, U), contradictions(U, Contra),
	findall(X, (member(Y, Contra), X = ((A2, P) ⊦ (Y ∧ ¬(Y)))), NextStepList),
	disjunction_list(NextStepList, NextStep),
	findall(X, (member(Y, Contra), 
				format(atom(X), '"~w": ["~w", "~w", "~w", "~w"]', 
					   [N, origin_node(C), edge(C, ¬(C)), edge(Y ∧ ¬(Y), ¬(C)), rule('¬I')])),
			NegIList),
	disjunction_list(NegIList, NegI).


proof(Derivation, [], G, G, N, N) :- 	
		isvalid(Derivation).

proof(Derivation, Proof, G, G, N, M) 	:- 	
		Derivation = (D1 ∧ D2),
		proof(D1, Proof1, _, _, N, NN), proof(D2, Proof2, _, _, NN, M), 
		union(Proof1, Proof2, Proof).

proof(Derivation, Proof, G, G, N, M) :- 	
		not(isvalid(Derivation)),
		rule(Derivation, NextStep, Gin, N), 
		succ(N,NN), 
		proof(NextStep, Proof1, Gin, Gout, NN, M),
		union([Gout],Proof1,Proof).

proof(Derivation, Proof, Gin, Gout, N, M) :- 
		Derivation = (D1 ∨ _),
		Gin = (G1 ∨ _),
		proof(D1, Proof, G1, Gout, N, M).

proof(Derivation, Proof, Gin, Gout, N, M) :- 
		Derivation = (_ ∨ D2),
		Gin = (_ ∨ G2),
		proof(D2, Proof, G2, Gout, N, M).



proof(Derivation, Proof) :- 
	Derivation = ((A, []) ⊦ _),
	findall(X, (member(Y, A), term_to_atom(origin_node(Y), X)), AStrings),
	term_to_atom(AStrings, Assumptions),
	format(atom(Assume), '"0": ~w', [Assumptions]),
	proof(Derivation, Proof1, _, _, 1, _),
	union([Assume], Proof1, Proof).


% Examples
% ?- proof((([¬(q),p→q], []) ⊦ ¬(p)), P).
%


proof_py(Derivation, Proof) :-
	proof(Derivation, Proof1), 
	term_to_atom(Proof1, Proof).