% Binding strength of operators, from strong to weak:
% negation: 800
% conjunction: 801
% disjunction: 802
% implication: 803
% equivalence: 804

:- op(800, fy, ¬).
:- op(801, yfx, ∧).
:- op(802, yfx, ∨).
:- op(803, xfx, →).
:- op(804, xfx, ↔).


:-use_module(my_term).


read_file(File, Rules) :-
    open(File, read, Stream),
    read_rules(Stream, Rules),
    close(Stream).

read_rules(Stream, []) :-
    at_end_of_stream(Stream).

read_rules(Stream, [Rule | Rules]) :-
    \+ at_end_of_stream(Stream),
    read_line_to_string(Stream, Line),
    split_string(Line, "⊢", "", [Left, Right]),
    Rule = (Left, Right),
    read_rules(Stream, Rules).


rule(LIn, LOut, I) :-
    read_file('../data/axioms.txt', Rules),
    nth1(I, Rules, (Left, Right)),
    split_string(Left, ",", "", LeftList),
    forall(member(Axiom, LeftList), (atom_string(A, Axiom), member(A, LIn))),
    atom_string(C, Right),
    \+ member(C, LIn),
    LOut = [C|LIn].







% Definition of subformula
subformulas(Formula, Subformulas) :- 
            flatten_terms(Formula, Subformulas).

% Definition of subformula based on a list of formulas. 
subformulas_list(FormulaList, Subformulas) :-
    maplist(subformulas, FormulaList, Subformulas).

% Check if Subformula is in the list of subformulas in FormulaList. 
has_subformas_list(FormulaList, Subformula) :-
    maplist(subformulas, FormulaList, Subformulas), member(Subformula, Subformulas).


% Rules of elimination (performed on premisses)
% Define the predicate rule1/2 (and-elimination, from X and Y we can conclude X.)
rule1([C|R], LOut) :-
    (member(X∧_Y, R), \+ member(X, R), !, R1 = [X|R], LOut = [C|R1]).


% Define the predicate rule1/2 (and-elimination, from X and Y we can conclude Y.)
rule2([C|R], LOut) :-
    (member(_X∧Y, R), \+ member(Y, R), !, R1 = [Y|R], LOut = [C|R1]).

% Define the predicate rule3/2 (equivalence-elimination, from X equivalence Y we can conclude (X implies Y) and (Y implies X))
rule3([C|R], LOut) :-
    (member(X↔Y, R), \+ member((X→Y)∧(Y→X), R), !, R1 = [(X→Y)∧(Y→X)|R], LOut = [C|R1]).

% Define the predicate rule3/2 (implication-elimination, from X implies Y and X we can conclude Y.)
rule4([C|R], LOut) :-
    (member(X→Y, R), member(X, R), \+ member(Y, R), !, R1 = [Y|R], LOut = [C|R1]).

% Define the predicate rule4/2 (disjunction-elimination, from X or Y and X implies Z and Y implies Z we can conclude Z.)
rule5([C|R], LOut) :-
    (member(X∨Y, R), member(X→Z, R), member(Y→Z, R), \+ member(Z, R), !, R1 = [Z|R], LOut = [C|R1]).

% Define the predicate rule7/2 (or-introduction, if C = X or Y then it is sufficient to conclude X.)
rule6([C|R], LOut) :-
	(C = (X↔Y), !, LOut = [(X→Y)∧(Y→X)|R]).
rule6b([C|R], LOut) :-
    (member((X→Y)∧(Y→X), R), \+ member(X ↔ Y, R), 
    has_subformas_list([C|R], X↔Y), !, R1 = [X↔Y|R], LOut = [C|R1]).

% Define the predicate rule7/2 (and-introduction, if C = X or Y then it is sufficient to conclude X.)
rule7([C|R], LOut) :-
    member(X, R), member(Y, R), \+ member(X∧Y, R), 
    has_subformas_list([C|R], X∧Y), !, R1=[X∧Y|R], LOut = [C|R1].

% Define the predicate rule7/2 (or-introduction, if C = X or Y then it is sufficient to conclude X.)
rule8a([C|R], LOut) :-
	(C = (X∨_Y), !, LOut = [X|R]).

% Define the predicate rule7/2 (or-introduction, if C = X or Y then it is sufficient to conclude X.)
rule8b([C|R], LOut) :-
    (C = (X∨Y), subformas_list([C|R], SL), member(Y, SL), has_subformas_list([C|R],X∨Y),!,LOut = [X|R]).


% Define the predicate rule7/2 (or-introduction, if C = X or Y then it is sufficient to conclude Y.)
rule9a([C|R], LOut) :-
	(C = (_X∨Y), !, LOut = [Y|R]).
rule9b([C|R], LOut) :-
    (C = (X∨Y), subformas_list([C|R], SL), member(X, SL), has_subformas_list([C|R],X∨Y),!,LOut = [X|R]).


% Define the predicate rule8/2 (implication-introduction, if C = X → Y then by expanding R with X it is sufficient to conclude Y.)
rule10([C|R], LOut) :-
	(C = (X→Y), member(X, R), !, LOut = [Y|R]);
	(C = (X→Y), !, R1 = [X|R], LOut = [Y|R1]).

% Define the predicate rule8/2 (negation-introduction, for any conclusion ¬(D) it is sufficient to show this conclusion by assuming D). 
rule11([C|R], LOut) :-
	(C = ¬(D), \+ member(D, R), \+ member(¬(¬(D)), R), !, R1 = [D|R], LOut = [C|R1]).

% Define the predicate rule8/2 (negation-elimination, for any conclusion C it is sufficient to show this conclusion by assuming ¬(C)). 
rule12([C|R], LOut) :-
	(\+ member(¬(C), R), (C = ¬(D) -> \+ member(D, R); true), !, R1 = [¬(C)|R], LOut = [C|R1]).

%If C appears in R we are done.
valid(L, [C|R]) :-
	(L = [C|R], member(C, R)).

% If we can find some contradiction, the proof is successful
% The rule negation-elimination is fullfilled, we are done.
valid(L, [C|R]) :-
	(L = [C|R], member(¬(C), R), member(X, R), member(¬(X), R)).

% The rule negation-introduction is fullfilled, we are done.
valid(L, [¬(D)|R]) :-
	(L = [¬(D)|R], member(D, R), member(X, R), member(¬(X), R)).


apply_rule_optimized(_, [], BestFL, BestFL, _).
apply_rule_optimized(L, [Rule|Rules], CurrentBestFL, BestFL, MaxDepth) :-
    ((call(Rule, L, FL), NewDepth is MaxDepth - 1, NewDepth >= 0, proof_with_depth(FL, R, NewDepth)) ->
        length([FL|R], LenFL),
        (LenFL > MaxDepth -> fail;
            (CurrentBestFL == none -> NewBestFL = [FL|R], NewBestLen = LenFL;
            length(CurrentBestFL, LenCurrentBestFL),
            (LenFL < LenCurrentBestFL -> NewBestFL = [FL|R], NewBestLen = LenFL;
            NewBestFL = CurrentBestFL, NewBestLen = LenCurrentBestFL)),
            apply_rule_optimized(L, Rules, NewBestFL, BestFL, MaxDepth))
    ;
        apply_rule_optimized(L, Rules, CurrentBestFL, BestFL, MaxDepth)
    ).


apply_rules(L, BestFL, MaxDepth) :-
    Rules = [rule1, rule2, rule3, rule4, rule5, rule6, rule8, rule9, rule10, rule11, rule12],
    apply_rule_optimized(L, Rules, none, BestFL, MaxDepth), \+ BestFL == none.


proof_with_depth_helper(L, Seq, Depth, MaxIter) :-
    (Depth =< MaxIter ->
        (proof_with_depth(L, Seq, Depth) -> true, !;
         (NewDepth is Depth + 1, proof_with_depth_helper(L, Seq, NewDepth, MaxIter)))
    ).

proof_with_depth(L, [], _) :-
	valid(L, L), !.
proof_with_depth([X ∧ Y|R], Seq, MaxDepth) :-
	proof_with_depth([X|R], Seq1, MaxDepth),
	proof_with_depth([Y|R], Seq2, MaxDepth),
	append(Seq1, Seq2, Seq), length(Seq, N), N =< MaxDepth.
proof_with_depth([C|R], Seq, MaxDepth) :-
    member(¬(D), R), \+ member(D, R),
    (member(¬(C), R); (C = ¬(F) -> \+ member(F, R); false)),
    NewDepth is MaxDepth - 1, NewDepth >= 0, C \= D, \+ D=.. [¬, _],
    proof_with_depth([D|R], Seq1, NewDepth), append([[C|R]], Seq1, Seq).
proof_with_depth(L, FL, MaxDepth) :-
    apply_rules(L, FL, MaxDepth).



proof(L, Seq, MaxIter) :-
    proof_with_depth_helper(L, Seq, 0, MaxIter).





%rule1([A, A => B], [A, A => B, B]).
%rule2([A => B, B => C], [A => B, B => C, A => C]).



% Definition des Zustandsraums
% state(+Statements, +AppliedRules, +StepCount)

% Definition des Aktionraums
% action(+Rule)

% Definition der Belohnungsfunktion
% reward(+NewStatements, +GoalStatements)

% Definition der Lernstrategie
% q_learning(+State, +Action, +Reward, +NewState)

% Initialisierung des Q-Tables
:- dynamic q_table/3.
q_table([], [], 0.0).


% Setzen des Agenten in den Anfangszustand
reset_agent(State) :-
    retractall(current_state(_)),
    assertz(current_state(State)).

% Definition des Startzustands
initial_state(State) :-
    State = state([p, p => q], [], 0).

% Definieren des Zielzustands
goal_state(state([p, q, p => q], _)).

% Setzen des Ziels
set_goal(GoalState) :-
    retractall(dynamic_goal_state(_)),
    asserta(dynamic_goal_state(GoalState)).

% Definieren des Zielzustands
dynamic_goal_state(state([p, q, p => q], _)).

% Definition des Aktionraums
legal_actions(AvailableRules) :-
    AvailableRules = [rule1, rule2].

% Definition der Belohnungsfunktion
reward(NewStatements, GoalStatements, Reward) :-
    length(NewStatements, NewStatementsLength),
    length(GoalStatements, GoalStatementsLength),
    Reward is 1 / abs(NewStatementsLength - GoalStatementsLength).

% Definition der Q-Lernfunktion
q_learning(State, Action, Reward, NewState) :-
    % Erhalten der aktuellen Q-Value für den aktuellen Zustand und die ausgewählte Aktion
    q_table(State, Action, QValue),
    % Erhalten der legalen Aktionen für den neuen Zustand
    legal_actions(AvailableRules),
    % Auswahl der besten Aktion für den neuen Zustand
    best_action(NewState, AvailableRules, BestAction),
    % Erhalten des Q-Values für den neuen Zustand und die beste Aktion
    q_table(NewState, BestAction, BestQValue),
    % Berechnung des neuen Q-Values basierend auf der Bellman-Gleichung
    NewQValue is QValue + LearningRate * (NewReward + DiscountFactor * MaxQValue - QValue),
    % Aktualisierung des Q-Tables mit dem neuen Q-Value
    update_q_table(CurrentState, Action, NewQValue),
    % Update des Zustands zum neuen Zustand
    NextState = NewState.



take(0, _, []) :- !.
take(_, [], []) :- !.
take(N, [X|Xs], [X|Ys]) :-
    N > 0,
    M is N-1,
    take(M, Xs, Ys).

random_goal_state(State) :-
    goal_state(state(GoalStatements, _)),
    length(GoalStatements, N),
    random_permutation(GoalStatements, RandomStatements),
    length(RandomStatements, M),
    K is min(N, M),
    take(K, RandomStatements, Statements),
    State = state(Statements, []).



% Training des Modells
train(N) :-
    initial_state(CurrentState),
    repeat,
        random_goal_state(GoalState),
        run_episode(CurrentState, GoalState),
        update_q_values(N),
    !.

% Führt eine Episode aus
run_episode(CurrentState, GoalState) :-
    % Anfangszustand
    reset_agent(CurrentState),
    % Zufälliges Ziel
    set_goal(GoalState),
    % Schleife, bis Ziel erreicht ist
    repeat,
        % Auswahl der Aktion
        select_action(Action),
        % Aktualisierung des Zustands und der Belohnung
        update_state_and_reward(Action, NextState, Reward),
        % Aktualisierung des Q-Values
        q_learning(CurrentState, Action, Reward, NextState),
        % Überprüfung, ob das Ziel erreicht wurde
        goal_state(NextState),
    !.
