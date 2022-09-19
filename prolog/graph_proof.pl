%  Basic libary to prove theorems
%    Author:        Martin Kunze
%    E-mail:        mkunze86@gmail.com
%    Copyright (c)  2022, Martin Kunze

:- module(graph_proof, [
				   		merge_rule_graph/5,
				   		get_assumptions_of/3,
				   		length_proof_graph/2,
				   		remove_not_sufficcient_vertices/3
				   		]).
:-use_module(graph).
:-use_module(set).


% Merges the subgraph of some rule into the BaseGraph.
% Example-Call:
% ?- merge_rule([(∧(a,b))],a,"∧E",graph([],[]),G).
% G = graph([a, ∧(a, b)], [edge(∧(a, b), a, "∧E")]).
merge_rule_graph(Assumptions, Conclusion, RuleName, GIn, GOut) :-
	findall(X, (A ∈ Assumptions, X = edge(A, Conclusion, RuleName)), EL),
	generate_weighted_graph(EL, G1),
	merge_graphs(G1, GIn, GOut).

get_assumptions_of(graph(V, E), Of, Assumptions) :-
	findall(X, (X ∈ V, edge(_, X, _) ∉ E, find_path_weighted(graph(V, E), X, Of, _)), Assumptions).

length_proof_graph(graph(_, E), N) :-
	findall(X, (edge(_, X1, X2) ∈ E, X = [X1, X2]), Rules),
	length(Rules, N).

remove_not_sufficcient_vertices(Conclusion, graph(VIn, EIn), graph(VOut, EOut)) :-
	findall(X, (X ∈ VIn, find_path_weighted(graph(VIn, EIn), X, Conclusion, _)), Sufficient),
	subtract(VIn, Sufficient, NotSufficient),
	delete_vertices_weighted(NotSufficient, graph(VIn, EIn), graph(VOut, EOut)).
