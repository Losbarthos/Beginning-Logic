% Prints dictionary varlues in a way, every value is on a seperate line in the terminal.
portray(Term) :-
	is_list(Term),
	write_term(Term, [max_depth(0)]).
portray(Term) :-
    is_dict(Term),
    dict_pairs(Term, Tag, Pairs),
    writef("%p{\n", [Tag]),
    foreach(member(Key-Value, Pairs), writef("\t%p: %p\n\n", [Key, Value])),
    write("}").


% Converts some string into some dictionary.  
alphabeth(ABC, IndexList, Dict) :-
	string_length(ABC, N), numlist(1, N, IndexList), 
	string_chars(ABC, V), 
	pairs_keys_values(KV, IndexList, V),
	dict_pairs(Dict, alphabeth, KV).

go(I, D) :- 	
	set_prolog_flag(answer_write_options,[max_depth(0)]),
	alphabeth("abcdefghijklmnopqrstuvwxyz", I, D).

go_debug :-
    %set_prolog_flag(color_term, false),
    protocol('test.txt'),
    %leash(-all),
    trace(numlist/3),
    trace(alphabeth/3),
    alphabeth("abcdefghijklmnopqrstuvwxyz", _I, _D),
    !,
    nodebug,
    noprotocol.
go_debug :-
    nodebug,
    noprotocol.
