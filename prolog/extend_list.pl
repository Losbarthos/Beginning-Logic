:- module(extend_list, [
				   		replace/4
				   		]).


% replace +O, +R, +ListOrigin, -ListReplacement
% write Prolog script for replacement any given element in lists by an another given element. For example:
% replace( 3, a,[1,2,3,4,3,5], [1,2,a,4,a,5])=true
% source: https://stackoverflow.com/questions/5850937/prolog-element-in-lists-replacement

replace(_, _, [], []).
replace(O, R, [O|T], [R|T2]) :- replace(O, R, T, T2).
replace(O, R, [H|T], [H|T2]) :- H \= O, replace(O, R, T, T2).