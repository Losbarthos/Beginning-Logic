%  Basic libary to introduce set operators
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(test, [
    (:=)/2, op(699, xfx, :=),
    op(598, xfy, ∪),
    op(597, xfy, ∩)
]).

union_((A ∪ B), C, D) :- union_(A, B, X), union_(X, C, D).
union_(A, (B ∪ C), D) :- union_((A ∪ B), C, D).
union_(A, B, C) :- is_list(A), is_list(B), union(A, B, C).

intersection_((A ∪ B), C, D) :- intersection_(A, B, X), intersection_(X, C, D).
intersection_(A, (B ∪ C), D) :- intersection_((A ∪ B), C, D).
intersection_(A, B, C) :- intersection(A, B, C).

C := (A ∪ B) :- union_(A, B, C).
C := (A ∩ B) :- intersection_(A, B, C).