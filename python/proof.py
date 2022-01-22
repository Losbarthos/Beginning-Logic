from config import *

import pandas as pd


from igraph import Graph, plot


class Proof:
	def __init__(self, assumptions, conclusion):
		self.assumptions = assumptions
		self.conclusion = conclusion
		self.theorems = self.build_derivations(CSV_THEOREMS)
		self.graph = self.init_graph()

	def init_graph(self):
		N = len(self.assumptions)

		# Defines a directed graph with assumptions 
		# and conclusion as vertices  
		g = Graph(directed=True)
		g.add_vertices(N + 1)

		g.vs["label"] = (self.assumptions 
		              + [self.conclusion])
		g.vs["category"] = ([Definition.ASSUMPTION] * N  
		                 + [Definition.CONCLUSION])

		return g

	def build_derivations(self, filename):
		derivations = {}

		def build_derivation(row):
			conclusion = row[CONCLUSION]
			assumptions = (row.dropna()
							  .filter(regex = f"^{ASSUMPTION}").values)

			derivations[row.name] = f"({assumptions} ⊦ {conclusion})"

		df = pd.read_csv(filename, index_col="Name")
		df.apply(build_derivation, axis=1)

		print(derivations)

		print(df)
		return df

	def proof():
		df.apply(body_fro_loop, axis=1)

	def show_graph(self, graph):
		layout = graph.layout("kk")
		plot(graph, layout=layout)


p = Proof(["p", "(p→q)"], "q")
print(p.theorems)
p.build_derivations(CSV_THEOREMS)
p.show_graph(p.graph)



		