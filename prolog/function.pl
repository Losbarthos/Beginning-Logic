%  Basic libary for invariant operations
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(function,[ 	
		calc_power/4,	% +Value, -Argument, +Function, -Power
		preimage/1      % +X
    ]).

:- use_module(library(clpfd)).

% calculates the +Power and the +Argument of some function +Function with value +Value.
calc_power(Argument, Argument, _, 0).
calc_power(Value, Argument, Function, Power) :-
	Power #\= 0,
	Power #= Power_m1 + 1,
	Value =..[Function, Buffer],
	calc_power(Buffer, Argument, Function, Power_m1).

% checks if +X is a preimage, means their is no function +Fun with +Fun(Y) is X for some Y. 
preimage(X) :-
	not(X=..[_, _]).