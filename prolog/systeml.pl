:- module(systeml, [convert_to_systeml/2]).

:-use_module(set).

sysl_getIdx(ProofNIdx, ProofIdx) :-
	findall(Y, (nth1(Idx, ProofNIdx, [A, B, C, D]), Y = [A, Idx, B, C, D]), ProofIdx).

sysl_get_premiss_idx(Idx, [A, P | _], Proof) :-
	[A, Idx, P, _, _] ∈ Proof.

sysl_get_assumption_idx(Idx, Assumption, Proof) :-
	[_, Idx, Assumption, "A", []] ∈ Proof.


sysl_with_premisses(ProofIdx, ProofPrm) :-
	findall(Y, 
			   ([A, B, C, D, E] ∈ ProofIdx,
			   	findall(I, 
			   		       (X ∈ E, sysl_get_premiss_idx(I, X, ProofIdx), I < B),
			   		    UIdxs),
			   	sort(UIdxs,Idxs),
			   	Y = [A, B, C, D, Idxs]),
			ProofPrm).

sysl_with_assumptions(ProofPrm, ProofAss) :-
	findall(Y, 
			   ([A, B, C, D, E] ∈ ProofPrm,
			   	findall(I, 
			   		       (X ∈ A, sysl_get_assumption_idx(I, X, ProofPrm), I =< B),
			   		    UIdxs),
			   	sort(UIdxs,Idxs),
			   	Y = [Idxs, B, C, D, E]),
			ProofAss).

aggregate_assumptions(AIn, _, [], AIn) :- !.
aggregate_assumptions(AIn, TIn, Premisses, AOut) :-
	findall(A, (I ∈ Premisses, [A, I, _, _, _ ] ∈ TIn), ANested),
	append(ANested,AList),
	intersection(AList, AIn, AOut).

optimize_assumptions_(TIn, TOut) :-
	findall(E, (E1 ∈ TIn, E1 = [AIn, B, C, D, P],
			   aggregate_assumptions(AIn, TIn, P, AA),
			   sort(AA, AOut),
			   E =[AOut, B, C, D, P]), TOut).

optimize_assumptions(TIn, TIn) :- optimize_assumptions_(TIn, TIn), !.
optimize_assumptions(TIn, TOut):- optimize_assumptions_(TIn, TB), 
								  optimize_assumptions(TB, TOut).

convert_to_systeml(ProofIn, ProofSystemL) :-
	sysl_getIdx(ProofIn, ProofIdx),
	sysl_with_premisses(ProofIdx, ProofPrm),
	sysl_with_assumptions(ProofPrm, ProofAss),
	optimize_assumptions(ProofAss, ProofSystemL).