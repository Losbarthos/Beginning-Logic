%  Basic libary to trace something into log proof_trace.txt
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(my_trace, [
                     inc_space_counter/0,
                     dec_space_counter/0,
                     trace_constant/2,
                     trace_nl/0
]).

:- dynamic global_counter/1.

% Initialisiere die globale Variable mit Null
% To generate some protocol file, first initialize prolog_flag my_trace with:
% set_prolog_flag(my_trace, true).
global_counter(0).

inc_space_counter :-
    ( current_prolog_flag(my_trace, true)
    ->  global_counter(Count),
        retract(global_counter(Count)),
        NewCount is Count + 1,
        assertz(global_counter(NewCount))
    ;true).

dec_space_counter :-
    ( current_prolog_flag(my_trace, true)
    ->  global_counter(Count),
        retract(global_counter(Count)),
        NewCount is Count - 1,
        assertz(global_counter(NewCount))
    ;true).

% create_spaces(+N: positive_integer, -Spaces: atom) is det.
% Creates an atom consisting of N spaces.
% N - the number of spaces in the resulting atom
% Spaces - the resulting atom with N spaces
create_spaces(N, Spaces) :-
    % Create a list of N spaces
    length(SpacesList, N),
    maplist(=(' '), SpacesList),
    % Convert the list into an atom
    atom_chars(Spaces, SpacesList).


% traces a Constant to a specific Value
trace_constant(Constant, Value) :-
    (   current_prolog_flag(my_trace, true)
    ->  open('proof_trace.txt', append, Stream),
        %write(Stream, 'Global constant '),
        global_counter(N), create_spaces(N, Spaces),
        write(Stream, Spaces),
        write(Stream, Constant),
        write(Stream, ': '),
        write(Stream, Value),
        write(Stream, '\n'),
        close(Stream)
    ;   true
    ).
trace_nl() :-
    (   current_prolog_flag(my_trace, true)
    ->  open('proof_trace.txt', append, Stream),
        write(Stream, '\n'),
        close(Stream)
    ;   true
    ).
