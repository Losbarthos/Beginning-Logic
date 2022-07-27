%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(ldict,
    [ same_elements/2,                  % +L1, +L2
      merge_premisses/2,                % +BasePair, -ResultPair
      merge_premisses/3,                % +BasePair, -ResultPair, +ToMerge
      is_value_in_dict/2,               % +V, +D
      replace/4,                        % +O, +R, +ListOrigin, -ListReplacement
      list_to_dict/3,                   % +Values, +Tag, -Dict
      dict_length/2,                    % +Dict, -Length
      dict_min_index/2,                 % +Dict, -Min
      dict_max_index/2,                 % +Dict, -Max 
      dict_normalize/3,                 % +DictIn, +MinValue, -DictOut
      dict_proof_append_assumption/3,   % +Assumption, +DictIn, -DictOut
      dict_proof_append_last/10,        % +Assumptions, +PremissesOrigin, +PremissesNoOrigin, +Conclusion, +Rule, +DictIn, -DictOut
      dict_proof_append_first/10,       % +Assumptions, +PremissesOrigin, +PremissesNoOrigin, +Conclusion, +Rule, +DictIn, -DictOut
      dict_from_assumptions/2           % +Assumptions, -Dict
    ]).



% check if two lists have the same elements
same_elements(X,Y):-subset(X,Y), subset(Y,X).

%%%
% BasePair is of Form [A1, P1] with P1 = {ai1, ..., aik, [[Aj1, Pj1],...,[Ajn, Pjn]]} 
% {[[Aj1, Pj1],...,[Ajn, Pjn]]} is seperated by:
%       1. {[Ajl1, Pjl1], ... [Ajln, Pjln]}, with Ajlo ⊆ A1 
%       2. {[Ajp1, Pjp1], ... [Ajpq, Pjpq]}, whereby condition 1 is not satisfied 
% ResultPair is of Form [A1, P2] with P2 = {ai1, ..., aik} and
%%%
merge_premisses(BasePair, ResultPair) :-
    BasePair = [A1, P1], ResultPair = [A1, P],
    findall(Y, (member(X, P1),
                X = [_, _], merge_premisses(BasePair, [_, Y], X)), ToInvolve),
    append(ToInvolve, ToAppend1),
    findall(Y, (member(Y, P1),
                not(is_list(Y))), ToAppend2),
    union(P1, ToAppend1, P11), union(P11, ToAppend2, P112), sort(P112, Px),
    findall(Y, (member(Y, P1),
                Y = [A, _], subset(A, A1)), ToDelete),
    subtract(Px, ToDelete, P).    


%%%
%  ToMerge is a pair of assumptions A and premisses P = {ai1, ..., aik, [Aj1, Pj1], ..., [Ajn, Pjn]}, means ToMerge = [A, P]. 
%  BasePair has form [A1, P1].
%  ResultPair has form [A1, P2].
%  Now find all [Aj, Pj] ∈ ToMerge with Aj ⊆ A1 and collect the Pj in an set [Pj1, Pj2, ..., Pjn]
%  P2 = P1 ∪ Pj1 ∪ ... ∪ Pjn ∪ [ai1, ai2, ..., aik]
%%%
merge_premisses(BasePair, ResultPair, ToMerge) :-
    BasePair = [A1, P1], ResultPair = [A1, P],
    ToMerge = [A2, P2], subset(A2, A1),
    findall(Y, (member(Y, P2),
                Y = [A, _], not(subset(A, A1))), ToAppend1),
    findall(Y, (member(Y, P2),
                Y = [A, _], subset(A, A1)), ToInvolve),
    findall(Y, (member(X, ToInvolve),
                merge_premisses(BasePair, [_, Y], X)), InvolvedPairwise),
    append(InvolvedPairwise, ToAppend2),
    findall(Y, (member(Y, P2),
                not(is_list(Y))), ToAppend3),
    union(P1, ToAppend3, P3), union(P3, ToAppend2, P23), union(P23, ToAppend1, P123), sort(P123, P).
merge_premisses(BasePair, ResultPair, ToMerge) :-
    BasePair = [A1, P1], ResultPair = [A1, P],
    ToMerge = [A2, P2], not(subset(A2, A1)),
    union(P1, [ToMerge], P2), sort(P2, P).

% +V, +D
% checks if some value is in dict
%
is_value_in_dict(V, D) :-
  dict_pairs(D, _, P),
  pairs_keys_values(P, _, Vs),
  member(V, Vs).

% replace +O, +R, +ListOrigin, -ListReplacement
% write Prolog script for replacement any given element in lists by an another given element. For example:
% replace( 3, a,[1,2,3,4,3,5], [1,2,a,4,a,5])=true
% source: https://stackoverflow.com/questions/5850937/prolog-element-in-lists-replacement

replace(_, _, [], []).
replace(O, R, [O|T], [R|T2]) :- replace(O, R, T, T2).
replace(O, R, [H|T], [H|T2]) :- H \= O, replace(O, R, T, T2).

% list_to_dict(+Values, +Tag, -Dict)
% converts some list into a prolog dict (more details see: https://stackoverflow.com/questions/71893100/prolog-convert-list-into-dictionary)

list_to_dict(Values, Tag, Dict) :-
  findall(Key-Value, nth1(Key, Values, Value), Pairs),
  dict_create(Dict, Tag, Pairs).

% dict_length(+Dict, -Length)
% gets the length of some prolog dict

dict_length(Dict, Length) :-
  dict_pairs(Dict, _, Pairs),
  length(Pairs, Length).

% dict_min_index(+Dict, -Min)
% gets the min index (key) value of the dict

dict_min_index(Dict, Min) :-
  dict_pairs(Dict, _, Pairs),
  pairs_keys_values(Pairs, Keys, _),
  min_list(Keys, Min).

% dict_max_index(+Dict, -Max)
% gets the max index (key) value of the dict

dict_max_index(Dict, Max) :-
  dict_pairs(Dict, _, Pairs),
  pairs_keys_values(Pairs, Keys, _),
  max_list(Keys, Max).

% 
% Code for switching a dict of form
% dict_label{-N: a(-N), -N+1: a(-N+1), ..., -1: a(-1), 1: a(1), ..., M: a(M)}.
%
% into some dict of form
% dict_label{MindValue: a(MindValue), ..., M: a(M), M+1: a(-N), ..., M+N-MindValue: a(MindValue-1) }.
%
% whereby:
%  a(j), -N≤j≤M are the values of the dictionary with keys in the integer interval [-N, M]\{0}.
% More details see: https://stackoverflow.com/questions/71900566/prolog-how-to-switch-negative-indexes-of-dictionary-into-positive-successors-of/71901228#71901228

% dict_normalize(+DictIn, +MinValue, -DictOut)
dict_normalize(DictIn, MinValue, DictOut) :-
        dict_pairs(DictIn, Tag, Pairs), % transform dict into ordered list of pairs
        pairs_normalize(Pairs, MinValue, NewPairs), % work on the pairs to get the new dict
        dict_pairs(DictOut, Tag, NewPairs).

% dict_normalize(+PairsIn, +MinValue, -PairsOut)
pairs_normalize(PairsIn, MinValue, PairsOut) :-
        pairs_values(PairsIn, Values), % extract values
        pairs_keys(PairsIn, Keys), % extract keys
        keys_normalize(Keys, MinValue, NewKeys), % work on the keys to get the new list of pairs
        pairs_keys_values(PairsOut, NewKeys, Values).

% keys_normalize(+KeysIn, +MinValue, -KeysOut)
keys_normalize(KeysIn, MinValue, KeysOut) :-
        max_list(KeysIn, Max),
        Start is Max + 1, % determine the starting index for negative values
        keys_normalize(KeysIn, MinValue, Start, KeysOut). % this predicate works because keys are known to be ordered

keys_normalize([], _, _, []).
keys_normalize([H|T], MinValue, N, [N|NewT]) :- % negative key
        H < MinValue,
        !,
        NewN is N + 1,
        keys_normalize(T, MinValue, NewN, NewT).
keys_normalize([H|T], MinValue, N, [H|NewT]) :- % positive key (unchanged)
        keys_normalize(T, MinValue, N, NewT).


% appends a simplification of a premiss or assumption at the end of the dictionary,
% means, the simplification gets the last index in the dictionary.  
% +Assumptions, +PremissesOrigin, +PremissesNoOrigin, +PremissesExOrigin, +Conclusion, +Rule, 
% +DerivationOrigin, +DerivationNextStep, +DictIn, -DictOut
dict_proof_append_last(Assumptions, PremissesOrigin, PremissesNoOrigin, PremmissesExcOrigin,
                       Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut) :-
    dict_max_index(DictIn, AIndexIn), succ(AIndexIn, AIndexOut),
    sort(Assumptions, AssumptionsSort), term_string(assumptions(AssumptionsSort), StringAssumptions),
    term_string(premisses_origin(PremissesOrigin), StringPremissesOrigin),
    term_string(premisses_no_origin(PremissesNoOrigin), StringPremissesNoOrigin),
    term_string(premisses_exc_origin(PremmissesExcOrigin), StringPremmissesExcOrigin),
    term_string(conclusion(Conclusion), StringConclusion),
    string_concat("rule([", Rule, RuleLeft), string_concat(RuleLeft, "])", StringRule),
    term_string(d0(DerivationOrigin), StringDerivationOrigin), term_string(d1(DerivationNextStep), StringDerivationNextStep),
    dict_size(DictIn, S), Size is S + 1, term_string(step(Size), StringSize),

    DictOut = DictIn.put([AIndexOut = [StringAssumptions, 
                          StringPremissesOrigin, StringPremissesNoOrigin, StringPremmissesExcOrigin,
                          StringConclusion, StringRule, StringDerivationOrigin, StringDerivationNextStep, StringSize]]).

% appends a simplification of a premiss or assumption at the beginning of the dictionary,
% means, the simplification gets the first index in the dictionary.  
% +Assumptions, +PremissesOrigin, +PremissesNoOrigin, +PremissesExOrigin, +Conclusion, +Rule, 
% +DerivationOrigin, +DerivationNextStep, +DictIn, -DictOut
dict_proof_append_first(Assumptions, PremissesOrigin, PremissesNoOrigin, PremmissesExcOrigin,
                        Conclusion, Rule, DerivationOrigin, DerivationNextStep, DictIn, DictOut) :-
    dict_min_index(DictIn, CIndexIn), plus(CIndexOut, 1, CIndexIn),
    sort(Assumptions, AssumptionsSort), term_string(assumptions(AssumptionsSort), StringAssumptions),
    term_string(premisses_origin(PremissesOrigin), StringPremissesOrigin),
    term_string(premisses_no_origin(PremissesNoOrigin), StringPremissesNoOrigin),
    term_string(premisses_exc_origin(PremmissesExcOrigin), StringPremmissesExcOrigin),
    term_string(conclusion(Conclusion), StringConclusion),
    string_concat("rule([", Rule, RuleLeft), string_concat(RuleLeft, "])", StringRule),
    term_string(d0(DerivationOrigin), StringDerivationOrigin), term_string(d1(DerivationNextStep), StringDerivationNextStep),
    dict_size(DictIn, S), Size is S + 1, term_string(step(Size), StringSize),

    DictOut = DictIn.put([CIndexOut = [StringAssumptions, 
                          StringPremissesOrigin, StringPremissesNoOrigin, StringPremmissesExcOrigin,
                          StringConclusion, StringRule, StringDerivationOrigin, StringDerivationNextStep, StringSize]]).

% appends a assumption at proof dictionary.
% +Assumption +DictIn, -DictOut
dict_proof_append_assumption(Assumption, DictIn, DictOut) :-
    term_string(Assumption, StringAssumption),
    is_value_in_dict([StringAssumption, _], DictIn), 
    DictOut = DictIn.

dict_proof_append_assumption(Assumption, DictIn, DictOut) :-
    dict_max_index(DictIn, AIndexIn), succ(AIndexIn, AIndexOut), 
    term_string(Assumption, StringAssumption),
    dict_size(DictIn, S), Size is S + 1, term_string(step(Size), StringSize),
    not(is_value_in_dict([StringAssumption, _], DictIn)), 
    DictOut = DictIn.put([AIndexOut = [StringAssumption, StringSize]]).

% appends a assumption at proof dictionary.
% +Assumptions -Dict
dict_from_assumptions(Assumptions, Dict) :-
    length(Assumptions, N), numlist(1, N, Keys),
    findall(Y, (member(I, Keys), 
                nth1(I, Assumptions, X),
                term_string(X, StringX),
                term_string(step(I), StringSize),
                Y = [StringX, StringSize]), Values), 
    pairs_keys_values(Pairs, Keys, Values),
    dict_create(Dict, proof, Pairs).