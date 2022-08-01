%  Basic libary for invariant operations
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(invariant,[ 	
		invariant_2n/3,					% +X, +Y, +Fun
    	anymember_invariant_2n/3,		% +Terms, +Member, +F
    	remove_inv/3,                  	% +WithInv, -NoInv, +Inv
    	generator_inv/3,				% +Set, -Generator, +Inv)
    	generator_inv/4,				% +ListIn, -ListOut, +Inv, +Order
    	subset_inv/3,					% +Set, +SubSet, +Inv
    	union_inv/5						% +Set1, +Set2, -Set3, +Inv, +Order
    ]).

:-use_module(set).
:-use_module(function).




% The n-th solution of y arises from 2n times application of Fun by X.
% https://stackoverflow.com/questions/71967110/remove-invariants-from-some-prolog-list/71980981#71980981
% invariant_2n(+X,+Y,+Fun)

invariant_2n(X, Y, Fun) :-
    Y =.. [Fun, T],
    T =.. [Fun, X].
invariant_2n(X, Y, Fun) :-
    Y =.. [Fun, T],
    T =.. [Fun, Z],
    invariant_2n(X, Z, Fun).

% Checks, if their is some member in +Terms, which has negation invariant opposite to +Member 
% anymember_invariant_2n(+Terms,+Member,+F)
anymember_invariant_2n(Terms, Member, F) :-
	T ∈ Terms,
	invariant_2n(T, Member, F).
anymember_invariant_2n(Terms, Member, F) :-
	T ∈ Terms,
	invariant_2n(Member, T, F).


% Deletes all members of WithTemp with prefix Inv(...). 
% remove_inv(+WithTemp,-NoTemp, +Inv)
remove_inv(WithInv, NoInv, Inv) :-
	findall(X, (X ∈ WithInv, not(X=.. [Inv,_])), NoInv).

% Is able to convert invariant generator parameter +Inv (with Inv(a) = a) and some 
% list +ListIn of form [...ai ... Inv(bi)] into some list +ListOut 
% which has distinct members respect to +Inv and if a and Inv(b)=a are members of 
% +ListIn, then Inv(Inv(...(a)) (not a) is a member of +ListOut, where +Inv occurs +Order times.
generator_inv(ListIn, ListOut, Inv, Order) :-
	findall(X, ( Y ∈ ListIn,  
				 Z ∈ ListIn, 
				 not(Y = Z), 
				 calc_power(Y, X , Inv, _),
				 calc_power(Z, X , Inv, _),
				 preimage(X)), Roots),
	findall(X, (Y ∈ Roots,
				X ∈ ListIn,
				calc_power(X, Y , Inv, _)), ListSub),
	findall(X, (Y ∈ Roots,
				calc_power(X, Y , Inv, Order)), List1),
	subtract(ListIn, ListSub, ListBase),
	ListOutD := (ListBase ∪ List1),
	sort(ListOutD, ListOut).

% Removes the Inv-Prefix of all Members of +Set and stories it in +Generator.
generator_inv(Set, Generator, Inv) :-
	findall(X, (Y ∈ Set, X=..[Inv, Y]), NextSet),
	SetComplete := (Set ∪ NextSet),
	generator_inv(SetComplete, Generator, Inv, 0).

% True if all the +Inv-free generator elements of +SubSet belong to +Set.
subset_inv(Set, SubSet, Inv) :-
	generator_inv(Set, SetGen, Inv),
	generator_inv(SubSet, SubSetGen, Inv),
	subset(SetGen, SubSetGen).

% True if -Set3 unifies with the union of the lists +Set1 and +Set2. Invariant elements a and b by +Inv are substituted by 
% Inv(Inv(...Inv(x))) of order +Order.
union_inv(Set1, Set2, Set3, Inv, Order) :-
	Buffer := (Set1 ∪ Set2),
	generator_inv(Buffer, Set3, Inv, Order).
