:- module(systeml, [convert_to_systeml/2]).

:-use_module(set).

sysl_getIdx(ProofNIdx, ProofIdx) :-
	findall(Y, (nth1(Idx, ProofNIdx, [A, B, C, D]), Y = [A, Idx, B, C, D]), ProofIdx).

sysl_get_assumption_idx(Idx, Assumption, Proof) :-
	[_, Idx, Assumption, "A", []] ∈ Proof.
sysl_get_premiss_idx(Idx, [A, P | _], Proof) :-
	[A, Idx, P, _, _] ∈ Proof.


sysl_with_assumptions(ProofPrm, ProofAss) :-
	findall(Y, 
			   ([A, B, C, D, E] ∈ ProofPrm,
			   	findall(I, 
			   		       (X ∈ A, sysl_get_assumption_idx(I, X, ProofPrm)),
			   		    UIdxs),
			   	sort(UIdxs,Idxs),
			   	Y = [Idxs, B, C, D, E]),
			ProofAss).

sysl_with_premisses(ProofIdx, ProofPrm) :-
	findall(Y, 
			   ([A, B, C, D, E] ∈ ProofIdx,
			   	findall(I, 
			   		       (X ∈ E, sysl_get_premiss_idx(I, X, ProofIdx)),
			   		    UIdxs),
			   	sort(UIdxs,Idxs),
			   	Y = [A, B, C, D, Idxs]),
			ProofPrm).


convert_to_systeml(ProofIn, ProofSystemL) :-
	sysl_getIdx(ProofIn, ProofIdx),
	sysl_with_premisses(ProofIdx, ProofPrm),
	sysl_with_assumptions(ProofPrm, ProofSystemL).