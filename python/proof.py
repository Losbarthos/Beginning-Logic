from config import *

import pandas as pd


from igraph import Graph, plot



class Proof:
	def __init__(self, assumptions, conclusion):
		self.assumptions = assumptions
		self.conclusion = conclusion
		self.theorems = self.init_theorems(CSV_THEOREMS)
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

	def init_theorems(self, filename):
		theorems = {}

		def init_theorem(row):
			conclusion = row[CONCLUSION]
			assumptions = (list(row.dropna()
						  .filter(regex = f"^{ASSUMPTION}").values))
			theorems[f'"{row.name}"'] = (f"({assumptions} ⊦ {conclusion})"
											.replace("'", ""))

		df = pd.read_csv(filename, index_col="Name")
		df.apply(init_theorem, axis=1)
		
		theorems = (f'{theorems}'
					.replace("'", "")
					.replace('"', "'"))

		return theorems

	def proof(self):
		derivation = (f"{self.assumptions} ⊦ {self.conclusion}"
				     .replace("'", ""))
		for res in PL.query(f"usable_theorems_dict({derivation}, theorems{self.theorems}, Z)"):
				print(res)
	def show_graph(self, graph):
		layout = graph.layout("kk")
		plot(graph, layout=layout)


p = Proof(["p", "(p→q)"], "q")
p.proof()
p.show_graph(p.graph)



		