%  Basic libary for function operations
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(function,[ 	
		calc_power/4,	% +Value, -Argument, +Function, -Power
		root/3      	% +Image, -Preimage, +Function
    ]).

:- use_module(library(clpfd)).

% calculates the +Power and the +Argument of some function +Function with value +Value.
calc_power(Argument, Argument, _, 0).
calc_power(Value, Argument, Function, Power) :-
	Power #\= 0,
	Power #= Power_m1 + 1,
	Value =..[Function, Buffer],
	calc_power(Buffer, Argument, Function, Power_m1).

% checks if +Image is Function(Function(...(Function(Preimage))). 
root(Image, Image, Function) :-
	not(Image=..[Function, _]).
root(Image, Preimage, Function) :-
	Image=..[Function, Buffer],
	root(Buffer, Preimage, Function).