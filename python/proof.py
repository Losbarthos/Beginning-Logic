#  Basic libary to prove theorems
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze



from config import *

import tabulate as tbl

import pandas as pd

import networkx as nx
import matplotlib.pyplot as plt

from prolog_interface import PL_Interface

import json



def normalize(proposition):
	'''
		Replace proposition of form connective (proposition1, proposition2) 
		into proposition1 connective proposition2.
		Example: →(p, q) is converted into p → q.  
	'''
	try:
		rest = PL.query(f"binary_connective({proposition},A,B)".replace("'",""))[0]
		return f"({normalize(json_to_prolog(rest['A']))}{proposition[1]}{normalize(json_to_prolog(rest['B']))})"
	except:
		return proposition


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
	def __init__(self, network):
		self.len = 0
		self.graph = network.graph
		self.edge_labels = network.edge_labels
		self.indexes = invert_dict(network.edge_rule_index)
		self.node_description = self.description_set_false()
		self.table = self.create_table()


	def description_set_false(self):
		description = {}
		for node in self.graph.nodes:
			description[node] = False

		return description

	def get_table(self):
		df = self.table
		# remove brackets
		for c in df.columns:
			df[c]= df.apply(lambda x: str(x[c]).replace("[",'').replace(']',''), axis=1)
		return df.to_string(index=False, header=False)

	def create_table(self):
		table = self.init_assumptions()
		next_layer = table
		while False in self.node_description.values():
			next_layer = self.init_next_layer(next_layer)
		
		result = pd.DataFrame(next_layer)
		return result

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
			
			line = [assumption_index, index, proposition, rule_name, premisses]
			table.append(line)	
		return table	


	def init_assumptions(self):
		table = []
		for node in self.graph.nodes:
			if len(self.graph.in_edges(node)) == 0:
				self.len = self.len + 1
				self.node_description[node] = True
				
				assumption_index = [self.len]
				index = self.len
				proposition = node
				rule_name = 'A'
				premisses = ''

				line = [assumption_index, index, proposition, rule_name, premisses]
				table.append(line)
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
		for node in self.graph.nodes:
			if not nx.has_path(self.graph, node, self.conclusion):
				remove.append(node)
		
		for to_remove in remove:
			self.graph.remove_node(to_remove)

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
		self.derivation = derivation
		
		self.assumptions, self.conclusion = self.unzip(derivation)
		self.network = ProofNetwork(assumptions, conclusion)
		self.table = False
		self.rule_index = 0
		self.proofed()

	def set_index(self, index):
		self.rule_index = index

	def unzip(self, derivation):
		result = PL.query(f"unzip({derivation}, A, _, C).")[0]
		return (result['A'], result['C'])

	def proofed(self):
		'''
			Checks, if theorem is proofed.
		'''
		return PL.query(f"isvalid({self.derivation}).")



	def simplify(self, rule):
		result = PL.query(f"{rule}({self.derivation}, NextStep, Core).")
		if result != False:
			next_step = []
			core = []
			for step in result[0]['NextStep']:
				next_step.append(json_to_prolog(step).replace("'","").replace("(,","("))

			for elem in result[0]['Core']:
				core.append(normalize(json_to_prolog(elem)))
			
			return (next_step, core)
		return result

	def evaluate_and(self, rule, rule_result):
		derivations = rule_result[0]
		networks = []
		for derivation in derivations:
			proof_buffer = Proof(derivation)
			proof_buffer.set_index(self.rule_index)
			proof_buffer.proof()
			self.rule_index = proof_buffer.rule_index
			self.network.add_network(proof_buffer.network)

		head = rule_result[1][0]
		origin = rule_result[1][1:]
		self.network.connect_with_rule(rule, self.rule_index, head, origin)
		self.rule_index = self.rule_index + 1

	def proof(self):
		'''
			Core function for proving self.derivation.
		'''
		if self.proofed():	return True

		for key in BASIC_RULES:
			result = self.simplify(key)
			if result != False:
				if key in ['↓→']:
					self.evaluate_and(BASIC_RULES[key], result)

		self.network.remove_lost_vertices()	
		self.table = ProofTable(self.network) 


	


assumptions = ["(p→(q→r))", "(p→q)", "p"]
conclusion = "r"

derivation = f"([{','.join(assumptions)}],[]) ⊦ {conclusion}"

p = Proof(derivation)
p.proof()
print(p.table.get_table())
print(p.rule_index)
p.network.draw()

#p.show_graph(p.graph.graph)