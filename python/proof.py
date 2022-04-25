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

	def is_proven(self):
		'''
			True, if prove is already done.
		'''

		if self.original == None:
			return False
		else:
			return True

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
					if result == False:
						return False
					else:
						return [ast.literal_eval(item["Proof"].replace("proof","")) for item in result]
		derivation = self.derivation

		self.original = main(derivation)
		if self.original != False:
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
					try:
						premisses = premisses.union(set([select["Index"].item()]))
						assumptions = assumptions.union(select["Assumptions"].item())
					except:
						print(f"Table at moment: {df}")
						print(f"Indexes of most possible assumptions: {origin}")
						print(f"Premiss to append on table: {premiss}")
						raise ValueError('Proof table could not be created. The last index occurs at least 2 times in the previous propositions.')
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

		def is_unique_value(dictionary, key, value):
			to_append = True
			for index in dictionary:
				if dictionary[index].equals(value):
					to_append = False

			return to_append


		def main():
			'''
				Function init_tables(self) is called from here
			'''
			table = {}
			i = 0
			for proof in self.original:
				df = pd.DataFrame(
						   columns=['Assumptions', 'Index', 'Proposition', 'Premisses', 'Rule'])

				for key in proof:
					if type(proof[key]) is str: # assumptions are string objects
						new_frame = [df, assume(key, proof[key])]
					else: # general conclusions are list objects
						new_frame = [df, conclude(key, proof[key], df)]
					df = pd.concat(new_frame)	

				df.index = df['Index'] # sets key

				if is_unique_value(table, i, df):
					table[i] = df
					i = i + 1

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
					g.add_node(index)
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
		from netgraph._main import EmphasizeOnHoverGraph
		import matplotlib.pyplot as plt

		graph = self.graphs[index][0]
		edge_labels = self.graphs[index][1]
		color_map = self.graphs[index][2]
		node_labels = highlight = self.tables[index]
		node_labels = node_labels.to_dict()['Proposition']

		highlight = highlight.to_dict()["Assumptions"]
		highlight = {x: list(highlight[x].union(set([x]))) for x in highlight}
		fig, ax = plt.subplots(figsize=(10, 10))
		g = EmphasizeOnHoverGraph(graph, node_layout='dot',
			node_labels=node_labels, node_label_fontdict=dict(size=10),
			edge_labels=edge_labels, edge_label_fontdict=dict(size=8), edge_label_rotate=False,
			node_color=color_map, node_edge_color=color_map, arrows=True, mouseover_highlight_mapping = highlight
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


# MTT
# assumptions = ["(p→q)", "¬(q)"]
# conclusion = "¬(p)"
#