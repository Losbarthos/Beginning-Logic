#  Basic libary to prove theorems
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze



from config import *

from tabulate import tabulate

import pandas as pd

import networkx as nx
import matplotlib.pyplot as plt

from operator import itemgetter


#from swiplserver import json_to_prolog

import json

import multiprocessing



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

class ProofTable_next():
	def __init__(self, assumptions, next_conclusion, premisses = None, rule = None, previous_table = None):
		self.table = previous_table
		self.expand(assumptions, next_conclusion, premisses, rule_name)

	def expand(self, assumptions, next_conclusion, premisses, rule_name):
		for assumption in assumptions:
			self.add_assumption(assumption)


	def has_line(self, assumptions, proposition):
		'''
			Checks if the proof-table self.table already has some value with assumptions
			and proposition  
		'''
		assumption_indexes = []
		for assumption in assumptions:
			a_line = [el for el in self.table if el[4] == 'A' and el[2] == assumption]
			if len(a_line) == 0:
				return False
			else:
				assumption_indexes.append(a_line[1])
		assumption_indexes.sort()

		prop_line = [el for el in self.table if el[0] == assumption_indexes and el[2] == proposition]

		return len(a_line) > 0



	def add_assumption(self, assumption):
		index = 1
		if self.table != None:
			indexes = [el[1] for el in self.table]
			index = max(indexes) + 1

		if not self.has_line([assumption], assumption):
			line = [[index], index, assumption, '', 'A']
			self.table.append(line)

	def add_conclusion(self, assumptions, conclusion, rule, premisses):
		assumption_indexes = []
		premiss_indexes = []
		origin_indexes = []
		premisses_not_used = False

		for assumption in assumptions:
			a_line = [el for el in self.table if el[4] == 'A' and el[2] == assumption]
			assumption_indexes.append(a_line[1])

		for premiss in premisses:
			p_line = [el for el in self.table if el[2] == premiss and set(el[0]).issubset(set(assumption_indexes))]
			if len(p_line) == 0:
				premisses_not_used = True

			origin_indexes.append(p_line[0])
			premiss_indexes.append(p_line[1])


		lines = [el for el in self.table if el[0] == origin_indexes and el[2] == conclusion and el[3] == premiss_indexes]

		if len(lines) == 0:
			if premisses_not_used == True:
				indexes = [el[1] for el in self.table]
				index = min(indexes) - 1
				self.table.append(origin_indexes,index, conclusion, [], rule)
			else:
				indexes = [el[1] 
							for el in self.table 
								if el[0] == origin_indexes and el[2] == conclusion and el[3] == None and el[4] == rule]
				self.table = [[origin_indexes,indexes[0], conclusion, premiss_indexes, rule] 
								if item == [origin_indexes,indexes[0], conclusion, [], rule] 
								else item for item in self.table]


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
		self.derivation = derivation
		
		self.assumptions, self.premisses, self.conclusion = self.unzip(derivation, with_premisses=True, extended=True)
		self.network = ProofNetwork(self.assumptions, self.conclusion)
		
		self.table = ProofTable()
		self.table.expand_assumptions(self.assumptions)
		self.table.expand_premisses(self.premisses)

		self.rule_index = 0
		self.is_proofed = self.proofed()
	
	def replace_by(self, new_proof):
		self.derivation = new_proof.derivation
		
		self.assumptions = new_proof.assumptions
		self.premisses = new_proof.premisses
		self.conclusion = new_proof.conclusion
		self.network = new_proof.network
		
		self.table = new_proof.table
		
		self.rule_index = new_proof.rule_index
		self.is_proofed = new_proof.is_proofed	

	def set_index(self, index):
		self.rule_index = index

	def unzip(self, derivation, with_premisses=False, extended=False):
		result = PL.query(f"unzip({derivation}, A, B, C).")[0]
		result['A'] = json_to_prolog(result['A'])
		result['B'] = json_to_prolog(result['B'])
		result['C'] = json_to_prolog(result['C'])

		assumptions = normalize(result['A'], extended)
		premisses = normalize(result['B'], extended)
		conclusion = normalize(result['C'], extended)

		if with_premisses == False:
			return (assumptions, conclusion)
		else:
			return (assumptions, premisses, conclusion)

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
				next_step.append(normalize(json_to_prolog(step)))
			for elem in result[0]['Core']:
				res = normalize(json_to_prolog(elem), True)
				core.append(res)
			
			return (next_step, core)
		return result

	def expand_to_new_rule(self, subProofs, old_rule, new_rule):
		'''
			Updates the proof variables after one rule is successfully evaluated
			by functions evaluate_and or evaluate_or.
		'''
		
		# main function expand_to_new_rule:

		for subProof in subProofs:
			self.rule_index = subProof.rule_index
			self.network.add_network(subProof.network)

			self.table.expand_assumptions(subProof.table.assumptions)
			self.table.expand_premisses(subProof.table.premisses)

		head = new_rule[0]		
		origin = new_rule[1:]

		self.network.connect_with_rule(old_rule, self.rule_index, head, origin)
		self.rule_index = self.rule_index + 1
		self.is_proofed = True
		return True

	def evaluate_and(self, rule, rule_result):
		derivations = sring_to_stringlist(rule_result[0])
		proofs = []
		proof_index = self.rule_index

		for derivation in derivations:
			proof_buffer = Proof(derivation)
			proof_buffer.set_index(proof_index)

			proof_buffer.proof()

			if proof_buffer.is_proofed == False:	
				self.is_proofed = False
				return False

			proofs.append(proof_buffer)
			proof_index = proof_buffer.rule_index

		return proofs

	def evaluate_or(self, rule, rule_result):
		derivations = sring_to_stringlist(rule_result[0])
		if len(derivations) == 0:
			self.is_proofed = False
			return False

		n = len(derivations)
		proofs = []
			
		for i in range(n):
			p = Proof(derivations[i])
			p.set_index(self.rule_index)

			p.proof()

			if p.is_proofed == True:
				proofs.append([p, i, p.table.len, p.table.len])
		
		if len(proofs) == 0:
			self.is_proofed = False
			return False

		proofs = (sorted(proofs, key=itemgetter(3)))

		return [[proofs[0][0]], proofs[0][1], proofs[0][2]]


	def proof(self):
		'''
			Core function for proving self.derivation.
		'''
		question_solved = False
		passed = False
		protocoll_marked = False 
		neg_proof_buffer = []
		neg_index = 0 
		
		if self.is_proofed == False:	
			for key in BASIC_RULES:
				passed = False
				result = self.simplify(key)
				if result != False:
					if GET_PROTOCOLL == True:
						print("Old: " + self.derivation)
						print("Key: " + key)
						print(f"New: {result[0]}")
					
					if key in ['↓→', '↑∧']:
						passed = True
						question_solved = self.evaluate_and(BASIC_RULES[key], result)

						if question_solved != False:
							question_solved = self.expand_to_new_rule(question_solved, BASIC_RULES[key], result[1])
					elif key in ['↓¬¬', '↓¬']:
						buffer = self.evaluate_or(BASIC_RULES[key], result)
						if buffer != False:
							buffer.append(key)
							neg_proof_buffer.append(buffer)

						
						if key == '↓¬':
							passed = True
							try:
								neg_proof_buffer.remove(False)
							except:
								pass

						if neg_index == 1:
							if neg_proof_buffer == []:
								question_solved = False
							else:
								neg_proof_buffer = (sorted(neg_proof_buffer, key=itemgetter(2)))
								question_solved = neg_proof_buffer[0]
								key_solved = question_solved[3]

						neg_index = neg_index + 1

						if passed == True and question_solved != False:
							print
							question_solved = self.expand_to_new_rule(question_solved[0], BASIC_RULES[key_solved], result[1][question_solved[1]])
						
				if passed == True:
					if question_solved == True:			

						self.network.remove_lost_vertices()
						self.table.set_network(self.network)
						self.table.create_table()

						if GET_PROTOCOLL == True:
							print(f"Solved: {self.derivation}")
							protocoll_marked = True
							self.network.draw()
							
							print(tabulate(self.table.console_format(),  showindex=False, tablefmt="plain"))
						break
					else:
						if GET_PROTOCOLL == True:
							protocoll_marked = True
							print(f"Not solved: {self.derivation}")
		if GET_PROTOCOLL == True:
			if protocoll_marked == False:
				if self.is_proofed == True:
					print(f"Solved: {self.derivation}")
				else:
					print(f"Not solved: {self.derivation}")

	
if __name__ == '__main__':

	assumptions = ["(p→q)", "¬(q)"]
	conclusion = "¬(p)"

	derivation = f"([{','.join(assumptions)}],[]) ⊦ {conclusion}"


	print(derivation)

	p = Proof(derivation)

	p.proof()
	
	print(p.is_proofed)

	#p.table.create_table()

	
	print(tabulate(p.table.console_format(),  showindex=False, tablefmt="plain"))

#print(p.rule_index)
	p.network.draw()

	#p.network.show_graph(p.graph.graph)
#([(p→(q→r)),(p→q),p],[]) ⊦ r