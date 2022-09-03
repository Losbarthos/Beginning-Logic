%  Basic libary to introduce set operators
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- dynamic ⊥ /1.



get_next_element(N) :- not(⊥(N)), assert(⊥(N)).
get_next_element(N) :- ⊥(N), M is N + 1, get_next_element(M).

get_next() :- get_next_element(0).