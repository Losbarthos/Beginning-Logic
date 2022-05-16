%  Basic libary to for definitions/conventions of mathematical kind
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(definitions,[
	op(699, xfx, :=),
	op(599, xfy, ∪)
	]).

%:-op(699, xfx, :=).
%:-op(599, xfy, ∪).



C := (A ∪ B) :- union(A, B, C).
