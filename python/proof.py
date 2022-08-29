
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
		# full output of tables
		pd.set_option('display.max_rows', None)
		pd.set_option('display.max_columns', None)
		pd.set_option('display.width', None)
		pd.set_option('display.max_colwidth', None)
		
		# Constants
		self.NODE = "origin_node"
		self.EDGE = "edge"
		self.RULE = "rule"

		self.assumptions = []
		self.conclusion = ""

		self.derivation = ""
		self.s_graph = None
		self.s_table = None
		self.proof_derivations = None
		self.tables = None
		self.graphs = None

	def is_proven(self):
		'''
			True, if prove is already done.
		'''

		return self.s_graph

	def add_assumptions(self, assumptions):
		if(type(assumptions) == str ):
			self.assumptions.append(assumptions)
		else:
			self.assumptions = [*self.assumptions, *assumptions]
		self.update_derivation()

	def set_conclusion(self, conclusion):
		self.conclusion = conclusion
		self.update_derivation()

	def set_derivation(self, derivation):
		'''
			The variable derivation is a string of form '[a1, a2, ..., an] ⊢ c'.
		'''
		try:
			[assumptions, conclusion] = derivation.split('⊢')
			assumptions = assumptions.strip()
			assumptions = assumptions.strip('][').split(', ')
			conclusion = conclusion.strip()
			self.add_assumptions(assumptions)
			self.set_conclusion(conclusion)
		except:
			raise ValueError(f"derivation {derivation} could not be converted!")

	def update_derivation(self):
		self.derivation = f"[{','.join(self.assumptions)}] ⊢ {self.conclusion}"

	def get_derivation(self):
		if len(self.assumptions) == 0 and self.conclusion == "":
			return ""
		else:
			return f"{','.join(self.assumptions)} ⊢ {self.conclusion}"

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
					prolog_thread.query(f"consult('{PL_PROOF}').")
					result = prolog_thread.query(f"proof_py({derivation}, Graph, Table).")
					if result == False:
						return [False, False]
					else:
						graph = [item["Graph"] for item in result]
						table = [item["Table"] for item in result]
						return [graph, table]
		derivation = self.derivation

		[self.s_graph, self.s_table] = main(derivation)
		if self.s_graph != False:
			self.tables = self.init_tables()
			self.graphs = self.init_graphs()

	# From prolog-graph to python pandas-dataframe table 
	# More details see: https://stackoverflow.com/questions/73519055/convert-string-which-illustrates-some-list-into-pandas-dataframe
	def init_tables(self):
		import re
		from ast import literal_eval

		rows = []
		table = {}

		i = 0

		for tbl in self.s_table:
			# split at ',' followed by two closing ]]
			for x in re.split(r"(?<=\]\]),", tbl[1:-1]):
			    
			    # split at ',' after closing ] OR between '"' and opening [ 
			    left, middle, right = re.split(r"(?<=\]),(?=\d)|(?<=\"),(?=\[)", x[1:-1])

			    # split the middle part at ','
			    middle = middle.split(",")
			    
			    rows.append([literal_eval(left), *middle, literal_eval(right)])
			    


			df = pd.DataFrame(rows, columns=['Assumptions', 'Index', 'Proposition', 'Rule', 'Premisses'])

			columns_titles = ['Assumptions', 'Index', 'Proposition', 'Premisses', 'Rule']
			df=df.reindex(columns=columns_titles)

			df["Index"] = df.Index.astype(int)
			df["Assumptions"] = df.apply(lambda row: set(row["Assumptions"]), axis=1)
			df["Premisses"] = df.apply(lambda row: set(row["Premisses"]), axis=1)
			df["Rule"] = df.Rule.str.strip('"')
			df.index = df["Index"] # sets key
			table[i] = df
			i = i + 1

		return table


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
		
		import matplotlib
		import matplotlib.pyplot as plt
		matplotlib.use('GTK3Agg')
		
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

	p.set_derivation('[¬(q),p→q] ⊢ ¬(p)')
	
	p.proof()

	print(p.tables)
	p.view_graph(0)


# MTT
# assumptions = ["(p→q)", "¬(q)"]
# conclusion = "¬(p)"
#