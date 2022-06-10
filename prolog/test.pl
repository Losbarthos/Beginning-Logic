

nextA("Terra", "Michelle").
nextA("Terra", "Max").
nextA("Marie", "Claudia").
nextA("Ed", "Larissa").


nextB("Terra", "Tom").
nextB("Tom", "Bob").
nextB("Tom", "Karl").
nextB("Michelle", "Tom").
nextB("Michelle", "Ed").
nextB("Michelle", "Stephane").

cond1(Step, Solution) :-
	once(nextA(Step, NextStep)),
	relations(NextStep, Solution0),
	union([Step], Solution0, Solution).

relations(Step, Solution) :-
	cond1(Step, Solution).

relations(Step, Solution) :-
	not(cond1(Step, Solution)),
	nextB(Step, NextStep),
	relations(NextStep, Solution0),
	union([Step], Solution0, Solution).

relations(Step, [Step]) :- not(nextA(Step, S)), not(nextB(Step, S)).