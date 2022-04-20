#  Basic libary to prove theorems
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze



from config import *

from tabulate import tabulate

import pandas as pd

import networkx as nx
from anytree import Node, search
import matplotlib.pyplot as plt

from operator import itemgetter




def normalize(proposition, extended = False):
	'''
		Replace proposition of form connective (proposition1, proposition2) 
		into proposition1 connective proposition2.
		Example: →(p, q) is converted into p → q.  
	'''
	def normalize_list(list_data, extended=False):
		'''
		Converts some prolog list of propositions into some python list of propositions.
		'''
		result = PL.query(f"length({list_data}, N)")[0]
		n = int(result['N'])

		assumptions = []
		for i in range(n):
			result = PL.query(f"nth0({i},{list_data},N)")[0]
			result['N'] = json_to_prolog(result['N'])
			result['N'] = normalize(result['N'])
			assumptions.append(result['N'])

		if extended == False:
			return f"[{', '.join(assumptions)}]"
		else:
			return assumptions

	try:
		rest = PL.query(f"binary_connective({proposition},A,B)".replace("'",""))[0]
		return f"({normalize(json_to_prolog(rest['A']))} {proposition[1]} {normalize(json_to_prolog(rest['B']))})"
	except:
		try:
			rest = PL.query(f"unzip({proposition},A, P, C)")[0]
			rest['A'] = json_to_prolog(rest['A'])
			rest['A'] = normalize_list(rest['A'])
			rest['P'] = json_to_prolog(rest['P'])
			rest['P'] = normalize_list(rest['P'])
			rest['C'] = json_to_prolog(rest['C'])
			rest['C'] = normalize(rest['C'])
			return f"(({rest['A']}, {rest['P']}) ⊦ {rest['C']})"
		except:
			try:
				return normalize_list(proposition, extended)
			except:
				return proposition.replace("'","")

def sring_to_stringlist(list_data):
	result = PL.query(f"length({list_data}, N)")[0]
	n = int(result['N'])

	assumptions = []
	for i in range(n):
		result = PL.query(f"nth0({i},{list_data},N)")[0]
		result['N'] = json_to_prolog(result['N'])
		result['N'] = normalize(result['N'])
		assumptions.append(result['N'])

	return assumptions


def invert_dict(d):
	'''
		Inverts a dict
		Example:
		d = {'child1': 'parent1',
     		 'child2': 'parent1',
     		 'child3': 'parent2',
     		 'child4': 'parent2',
     		}
     	returns: {'parent2': ['child3', 'child4'], 'parent1': ['child1', 'child2']}
	'''
	from collections import defaultdict
	new_dict = defaultdict(list)
	for k, v in d.items():
		new_dict[v].append(k)

	return dict(new_dict)

class ProofTable():
	def __init__(self):
		self.len = 0
		self.assumptions = None
		self.premisses = None
		self.graph = None
		self.edge_labels = None

		# relation between indexes and edges which illustrate rules
		self.indexes = None
		# checks if node already used
		self.node_description = None
		self.table = None

		# for checking, which edges are 
		self.used_edges = None

	def set_network(self, network):
		self.graph = network.graph
		self.edge_labels = network.edge_labels
		self.indexes = invert_dict(network.edge_rule_index)
		self.node_description = self.description_set_false()

		self.used_edges = dict.fromkeys(network.graph.in_edges, False)


	def expand(self, base, to_expand):
		if base == None:
			base = to_expand
		else:
			[base.append(x) for x in to_expand if x not in base]		

		return base

	def expand_assumptions(self, assumptions):
		self.assumptions = self.expand(self.assumptions, assumptions)

	def expand_premisses(self, premisses):
		self.premisses = self.expand(self.premisses, premisses)

	def description_set_false(self):
		description = {}
		for node in self.graph.nodes:
			description[node] = False

		return description

	def console_format(self):
		'''
			Gets the ProofTable (without header-row and index-column) 
			into console-format. It is neccessary for further printing.
		'''

		df = self.table
		df = df.astype(str).apply(lambda col: col.str.strip('[]')) # remove brackets
		df[1] = df[1].apply(lambda val: f"({val})") # Brackets arround the Index-Column
		return df#.to_string(index=False, header=False)

	def create_table(self):
		table = self.init_assumptions()
		next_layer = table
		while False in self.node_description.values():
			next_layer = self.init_next_layer(next_layer)
		
		result = pd.DataFrame(next_layer)
		self.table = result

	def init_next_layer(self, table):
		def normalize_list(val):
			'''
				Removes duplicates from list and sort list values. 
			'''
			if len(val) == 0:
				return ""
			result = list(dict.fromkeys(val)) # removes duplicates from list
			result.sort()
			return result

		layer = []
		for value in self.indexes:
			buffer = True
			for edge in self.indexes[value]:
				if self.node_description[edge[0]] == False or self.node_description[edge[1]] == True:
					buffer = False
					break
			if buffer == True:
				layer.append(self.indexes[value])
				for edge in self.indexes[value]:
					self.used_edges[edge] = True
		

		for rule in layer:
			self.len = self.len + 1
			self.node_description[rule[0][1]] = True

			assumption_index = []
			premisses = []
			for edge in rule:
				search = edge[0]
				for line in table:
					if search in line:
						reference_line = line

				assumption_index = assumption_index + reference_line[0]
				premisses.append(reference_line[1])

			assumption_index = normalize_list(assumption_index) 
			premisses = normalize_list(premisses) 

			index = self.len
			proposition = edge[1]
			rule_name = self.edge_labels[rule[0]]
			
			line = [assumption_index, index, proposition, premisses, rule_name]
			table.append(line)	

		
		unused_edges = [k for k,v in self.used_edges.items() if v == False]
		

		if False not in self.node_description.values() and len(unused_edges) > 0:
			for edge in unused_edges:
				self.node_description[edge[1]] = False
		
		return table


	def init_assumptions(self):
		def assumption_line(index, assumption):
			assumption_index = [index]
			proposition = assumption
			rule_name = 'A'
			premisses = ''

			line = [assumption_index, index, proposition, premisses, rule_name]
			return line

		table = []
		node_assumptions = []

		for node in self.graph.nodes:
			if len(self.graph.in_edges(node)) == 0:
				node_assumptions.append(node) 

		assumptions = [x for x in self.assumptions if x not in self.premisses]

		self.expand(assumptions, node_assumptions)

		for assumption in assumptions:
			self.len = self.len + 1
			self.node_description[assumption] = True

			table.append(assumption_line(self.len, assumption))


		return table


class ProofNetwork():
	'''
		Object stores a grap with all his functionality in which the proof is stored.
	'''
	def __init__(self, assumptions, conclusion):
		self.assumptions = assumptions
		self.conclusion = conclusion
		self.graph = self.init_graph(self.assumptions, self.conclusion)
		self.edge_labels = {}
		self.edge_rule_index = {}


	def init_graph(self, assumptions, conclusion):
		'''
			Defines a directed graph with assumptions and the conclusion
			as vertices.
		'''
		g = nx.DiGraph()

		g.add_nodes_from(assumptions)
		g.add_node(conclusion)

		return g

	def connect_with_rule(self, rule_name, rule_index, head, origin):
		for vertex in origin:
			self.graph.add_edge(vertex, head)
			self.edge_labels[(vertex, head)] = rule_name
			self.edge_rule_index[(vertex, head)] = rule_index

	def add_network(self, network):
		self.edge_labels.update(network.edge_labels)
		self.edge_rule_index.update(network.edge_rule_index)

		self.graph = nx.compose(self.graph, network.graph)

	def remove_lost_vertices(self):
		remove = []

		remove_label = []
		remove_index = []
		for node in self.graph.nodes:
			if not nx.has_path(self.graph, node, self.conclusion):
				remove.append(node)

				# for removing edge_labels
				for edge in self.edge_labels:
					if edge[1] == node:
						remove_label.append(edge)

				# for removing edge_labels
				for edge in self.edge_rule_index:
					if edge[1] == node:
						remove_index.append(edge)
		
		for to_remove in remove:
			self.graph.remove_node(to_remove)
		
		# for removing edge_labels
		for edge in remove_label:
			self.edge_labels.pop(edge)
		# for removing edge_rule_index
		for edge in remove_index:
			self.edge_rule_index.pop(edge)



	def draw(self):
		'''
		Draws the graph.
		'''
		pos = nx.spring_layout(self.graph)

		nx.draw(self.graph, pos, with_labels=True)
		nx.draw_networkx_edge_labels(self.graph, pos,edge_labels=self.edge_labels)
		
		plt.axis('off')
		plt.show()






class Proof:
	'''
		Core class for prooving theorems.
	'''
	def __init__(self, derivation):
		# Constants
		self.NODE = "origin_node"
		self.EDGE = "edge"
		self.RULE = "rule"

		self.derivation = derivation
		self.original = self.proof()
		self.tables = self.init_tables()

		self.graphs = self.init_graphs()



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
		return main(derivation)

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
			g = nx.DiGraph()
			edge_labels = {}
			color_map = []

			for index, row in table.iterrows():
				if(row["Rule"] == 'A'):
					
					color_map.append("red")
				else:
					color_map.append("blue")
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
		import matplotlib.pyplot as plt

		graph = self.graphs[index][0]
		edge_labels = self.graphs[index][1]
		color_map = self.graphs[index][2]
		node_labels = self.tables[index]
		node_labels = node_labels.to_dict()['Proposition']

		pos = nx.spring_layout(graph)

		nx.draw(graph, pos, node_color = color_map)
		nx.draw_networkx_labels(graph, pos, labels=node_labels)
		nx.draw_networkx_edge_labels(graph, pos,edge_labels=edge_labels)
		
		plt.axis('off')
		plt.show()




		
	

	
if __name__ == '__main__':

	assumptions = ["(p→q)", "¬(q)"]
	conclusion = "¬(p)"

	derivation = f"([{','.join(assumptions)}],[]) ⊦ {conclusion}"


	print(derivation)

	p = Proof(derivation)
	p.view_graph(0)


