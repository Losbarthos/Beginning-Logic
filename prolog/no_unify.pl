:- module(no_unify, [
						is_member_of/2,
				   		is_nth1/3
				   		]).


is_member_of( X , [Y|_]  ) :- X == Y .
is_member_of( X , [_|Ys] ) :- is_member_of(X,Ys) .

is_nth1( N, L , E ) :- is_nth1( 1 , L , E , N ) .

is_nth1( N , [Y|_]  , X , N ) :- X == Y .
is_nth1( I , [_|Ys] , X , N ) :- J is I+1, is_nth1(J,Ys,X,N) .