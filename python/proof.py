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
		self.proofs_original = self.proof(self.derivation)
		self.graphs = self.init_graphs(self.proofs_original)
		self.tables = self.init_tables(self.proofs_original)



	def proof(self, derivation):
		'''
			Proofs the derivation within Prolog functionality and sends it from 
			Prolog to Python with swiplserver. The result is a list of dictionaries 
			which illustrate the proof-graph.
		'''
		def proof_to_dict(proof):
			'''
				Converts the result string in some dictionary python can work with
			'''

			import json
			result = "{" + proof.replace("''",'"').replace("'","")[1:-1] + "}"
			result = json.loads(result)

			return result

		def main(derivation):
			'''
				Called from here.
			'''

			from swiplserver import PrologMQI, PrologThread

			with PrologMQI() as mqi:
				with mqi.create_thread() as prolog_thread:
					prolog_thread.query(f"consult('{PL_LOGIC}').")
					result = prolog_thread.query(f"proof_py({derivation}, Proof).")

					result = [proof_to_dict(item["Proof"]) for item in result]
					
					return result

		return main(derivation)

	def init_graphs(self, proofs):
		def remove_node(node_string):
			'''
				removes the function tag self.NODE(inner) and returns inner.
			'''
			return node_string.replace(self.NODE,"")[1:-1]

		def remove_rule(rule_string):
			'''
				removes the function tag self.RULE(inner) and returns inner.
			'''
			return rule_string.replace(self.RULE,"")[1:-1]

		def remove_edge(edge_string):
			'''
				removes the function tag self.EDGE(inner1, inner2) and returns 
				(inner1, inner2) as tuple.
			'''
			edge_string = edge_string.replace(self.EDGE,"")[1:-1]
			edge_string = edge_string.split(",")
			return tuple(edge_string)

		def main(proofs):
			'''
				Called from here.
			'''
			import networkx as nx

			result = []
			for proof in proofs:
				g = nx.DiGraph()
				lbl = {}

				for key, list_value in proof.items():
					
					nodes = [remove_node(x) for x in list_value if x.startswith(self.NODE)]
					edges = [remove_edge(x) for x in list_value if x.startswith(self.EDGE)]
					rule = [remove_rule(x) for x in list_value if x.startswith(self.RULE)]
					
		
					if len(rule) > 0:
						rule = rule[0] # at most we have one rule

					for node in nodes:
						g.add_node(node)

					for edge in edges:
						g.add_edge(edge[0], edge[1])
						lbl[edge] = rule

				result.append(tuple([g, lbl]))

			return result

		return main(proofs)

	def init_tables(self, proofs):
		print(proofs)



		for proof in proofs:
			for key, list_value in proof.items():


	def view_graph(self, index):
		'''
			Draws self.graph[index].
		'''
		import networkx as nx
		import matplotlib.pyplot as plt

		graph = self.graphs[index][0]
		labels = self.graphs[index][1]

		pos = nx.spring_layout(graph)

		nx.draw(graph, pos, with_labels=True)
		nx.draw_networkx_edge_labels(graph, pos,edge_labels=labels)
		
		plt.axis('off')
		plt.show()




		
	

	
if __name__ == '__main__':

	assumptions = ["(p→q)", "¬(q)"]
	conclusion = "¬(p)"

	derivation = f"([{','.join(assumptions)}],[]) ⊦ {conclusion}"


	print(derivation)

	p = Proof(derivation)
	#p.view_graph(0)


