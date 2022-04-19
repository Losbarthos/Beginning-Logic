%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(swish_chat,
    [ list_to_dict/3,   % +Values, +Tag, -Dict
      dict_length/2,    % +Dict, -Length
      dict_min_index/2, % +Dict, -Min
      dict_max_index/2, % +Dict, -Max 
      dict_normalize/3  % +DictIn, +MinValue, -DictOut
    ]).

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
% dict_label{1: a(1), ..., M: a(M), M+1: a(-N), ..., M+N: a(-1) }.
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