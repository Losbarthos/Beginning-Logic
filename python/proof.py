#  Basic libary to prove theorems
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze



from config import *

import pandas as pd

from igraph import Graph, plot

from prolog_interface import PL_Interface

class Proof:
	def __init__(self, assumptions, conclusion):
		self.assumptions = assumptions
		self.conclusion = conclusion
		self.theorems = self.init_theorems(CSV_THEOREMS)
		self.graph = self.init_graph()

	def init_graph(self):
		'''
			Defines a directed graph with assumptions and the conclusion
			as vertices.
		'''
		N = len(self.assumptions)
  
		g = Graph(directed=True)
		g.add_vertices(N + 1)

		g.vs["label"] = (self.assumptions 
		              + [self.conclusion])
		g.vs["category"] = ([Definition.ASSUMPTION] * N  
		                 + [Definition.CONCLUSION])

		return g

	def init_theorems(self, filename):
		'''
			Metod for initializing the theorems from filename into 
			some string we can pass as prolog-parameter (prolog dictionary). 
		'''
		theorems = {}

		def init_theorem(row):
			conclusion = row[CONCLUSION]
			assumptions = (list(row.dropna()
						  .filter(regex = f"^{ASSUMPTION}").values))
			assumptions = PL_Interface().list_to_datastring(assumptions)
			theorems[row.name] = f"({assumptions} ⊦ {conclusion})"

		df = pd.read_csv(filename, index_col="Name")
		df.apply(init_theorem, axis=1)
		
		return f"theorems{PL_Interface().dict_to_datastring(theorems)}"

	def proof(self):
		'''
			Core function for proving [self.assumptions] ⊦ self.conclusion.
		'''
		derivation = (f"{self.assumptions} ⊦ {self.conclusion}"
				     .replace("'", ""))
		result = PL.query(f"usable_theorems_dict({derivation}, {self.theorems}, Z)")
		result = PL_Interface().get_rule(result[0]['Z'])
	
	def show_graph(self, graph):
		'''
			Illustrates proof as directed graph.
		'''
		layout = graph.layout("kk")
		plot(graph, layout=layout)

p = Proof(["p", "(p→q)"], "q")
p.proof()