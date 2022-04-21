#  Basic libary to prove theorems
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze



from config import *
import pandas as pd


class Proof:
	'''
		Core class for prooving theorems.
	'''
	def __init__(self):
		# Constants
		self.NODE = "origin_node"
		self.EDGE = "edge"
		self.RULE = "rule"

		self.assumptions = []
		self.conclusion = ""

		self.derivation = ""
		self.original = None
		self.tables = None
		self.graphs = None


	def add_assumptions(self, assumptions):
		if(type(assumptions) == str ):
			self.assumptions.append(assumptions)
		else:
			self.assumptions = [*self.assumptions, *assumptions]
		self.update_derivation()

	def set_conclusion(self, conclusion):
		self.conclusion = conclusion
		self.update_derivation()

	def update_derivation(self):
		self.derivation = f"([{','.join(self.assumptions)}],[]) ⊦ {self.conclusion}"

	def get_derivation(self):
		if len(self.assumptions) == 0 and self.conclusion == "":
			return ""
		else:
			return f"{','.join(self.assumptions)} ⊦ {self.conclusion}"

	def proof(self):
		'''
			Proofs the derivation within Prolog functionality and sends it from 
			Prolog to Python with swiplserver. The result is a list of dictionaries 
			which illustrate the proof-graph.
		'''

		def main(derivation):
			'''
				This function is called from proof(self, derivation)
			'''

			from swiplserver import PrologMQI, PrologThread
			import ast

			with PrologMQI() as mqi:
				with mqi.create_thread() as prolog_thread:
					prolog_thread.query(f"consult('{PL_LOGIC}').")
					result = prolog_thread.query(f"proof_py({derivation}, Proof).")

					return [ast.literal_eval(item["Proof"].replace("proof","")) for item in result]
		derivation = self.derivation

		self.original = main(derivation)
		self.tables = self.init_tables()
		self.graphs = self.init_graphs()

	def init_tables(self):
		def assume(index, assumption):
			'''
				Returns some assumption line in table.
			'''
			line = {'Assumptions': set([index]),
					'Index': index,
					'Proposition': assumption,
					'Premisses': set([]),
					'Rule': 'A'}
			return pd.DataFrame([line])

		def conclude(index, inner, df):
			'''
				Returns some conclusion line different frome assumption line in table.
			'''
			def get_parameters(name, function):
				'''
					Gets the parameters [a1, a2, ..., an] in form of a list
					of some function of type f1(a1, a2, ..., an).
				'''
				inner = function.removeprefix(name)[2:-2]
				return inner.split(",")

			premisses = set([]) # premiss parameter in table (column 3)
			assumptions = set([]) # assumption parameter in table (column 0) (includes ex, which must be seperately eliminated)
			origin = set([]) # possible assumptions from prolog output
			ex = set([]) # propositions which are eliminated from assumptions
			rule = "" # rule name
			conclusion = "" # proposition name
			
			for entry in inner:
				if entry.startswith("edge"): # appends premiss index and its assumption indexes to line
					[premiss, conclusion] = get_parameters("edge", entry)
					select = df.loc[(df['Proposition'] == premiss) & 
										(df['Assumptions'].apply(lambda x: x.issubset(origin)))]
					premisses = premisses.union(set([select["Index"].item()]))
					assumptions = assumptions.union(select["Assumptions"].item())
					conclusion = conclusion
				elif entry.startswith("rule"): # gets the rule name
					rule = get_parameters("rule", entry)[0]
				elif entry.startswith("assumptions"): # gets the possible assumptions 
					origin = set([df.loc[(df['Proposition'] == assumption) &
								         (df['Rule'] == 'A')]["Index"].item() 
								  for assumption in get_parameters("assumptions", entry)])
				elif entry.startswith("except"): # gets the exceptions which don't get the permission to be assumptions. 
					ex = set([df.loc[(df['Proposition'] == no_assumption) &
								  	  (df['Rule'] == 'A')]["Index"].item() 
								  for no_assumption in get_parameters("except", entry)])

			line = {'Assumptions': assumptions.difference(ex),
					'Index': index,
					'Proposition': conclusion,
					'Premisses': premisses,
					'Rule': rule}
			return pd.DataFrame([line])


		def main():
			'''
				Function init_tables(self) is called from here
			'''
			table = {}
			i = -1
			for proof in self.original:
				i = i + 1
				table[i] = pd.DataFrame(
						   columns=['Assumptions', 'Index', 'Proposition', 'Premisses', 'Rule'])

				for key in proof:
					if type(proof[key]) is str: # assumptions are string objects
						new_frame = [table[i], assume(key, proof[key])]
					else: # general conclusions are list objects
						new_frame = [table[i], conclude(key, proof[key], table[i])]
					table[i] = pd.concat(new_frame)	

				table[i].index = table[i]['Index']

			return table
		# Body of function init_tables(self)
		return main()

	def init_graphs(self):
		import networkx as nx
		graphs = []


		for key in self.tables:
			table = self.tables[key]
			rows = len(table)
			g = nx.DiGraph()
			edge_labels = {}
			color_map = {}

			for index, row in table.iterrows():
				if(row["Rule"] == 'A'):
					color_map[index] = "red"
				elif(index < rows):
					color_map[index] = "lightblue"
				else:
					color_map[index] = "blue"
				for premiss in row["Premisses"]:
					e = (premiss, index)
					edge_labels[e]  = row["Rule"]
					g.add_edge(*e)
			graphs.append((g, edge_labels, color_map))

		return graphs
					



	def view_graph(self, index):
		'''
			Draws self.graph[index].
		'''
		import networkx as nx
		from netgraph import Graph # pip install netgraph
		import matplotlib.pyplot as plt

		graph = self.graphs[index][0]
		edge_labels = self.graphs[index][1]
		color_map = self.graphs[index][2]
		node_labels = self.tables[index]
		node_labels = node_labels.to_dict()['Proposition']

		print(graph)


		Graph(graph, node_layout='dot',
			node_labels=node_labels, node_label_fontdict=dict(size=10),
			edge_labels=edge_labels, edge_label_fontdict=dict(size=8), edge_label_rotate=False,
			node_color=color_map, node_edge_color=color_map, arrows=True
		)

		plt.show()
	

	
if __name__ == '__main__':

	p = Proof()

	assumptions = ["(p→q)", "¬(q)"]
	conclusion = "¬(p)"

	p.add_assumptions(assumptions)
	p.set_conclusion(conclusion)
	
	p.proof()

	p.view_graph(1)


