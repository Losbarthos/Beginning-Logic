#  Basic libary to prove theorems
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze



from config import *

import pandas as pd

import networkx as nx
import matplotlib.pyplot as plt

from prolog_interface import PL_Interface

import json



class ProofNetwork():
	'''
		Object stores a grap with all his functionality in which the proof is stored.
	'''
	def __init__(self, assumptions, conclusion):
		self.graph = self.init_graph(assumptions, conclusion)
		self.edge_labels = {}

	def init_graph(self, assumptions, conclusion):
		'''
			Defines a directed graph with assumptions and the conclusion
			as vertices.
		'''
		g = nx.DiGraph()

		g.add_nodes_from(assumptions)
		g.add_node(conclusion)

		return g

	def connect_rule(self, name, derivation):
		'''
		If "[a1, ..., an ] ⊦ c" is some rule with name 'rule', then expands the graph by 
		edges a1 -- c, ..., an -- c (edgename 'rule')
		:param derivation: string of form "[a1, ..., an ] ⊦ c"
		:param name: name of derivation
		'''
		def unpack_derivation(derivation):
			'''
			Converts some derivation "[a1, ..., an ] ⊦ c" into its assumptions 
			["a1", ..., "an"] and its conclusion "c".
			:param derivation: string of form "[a1, ..., an ] ⊦ c"
			'''
			result = PL.query(f"binary_derivation({derivation}, X, Y).")
			assumptions = PL_Interface().swipl_to_formula_list(result[0]['X'])
			conclusion = PL_Interface().swipl_to_formula(result[0]['Y'])

			return [assumptions, conclusion]

		[assumptions, conclusion] = unpack_derivation(derivation)
	
		for assumption in assumptions:
			self.graph.add_edge(assumption, conclusion)
			self.edge_labels[(assumption, conclusion)] = name
	
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
	def __init__(self, assumptions, conclusion):
		self.network = ProofNetwork(assumptions, conclusion)

		self.assumptions = assumptions
		self.conclusion = conclusion
		self.theorems = self.init_theorems(CSV_THEOREMS)


	def init_theorems(self, filename):
		'''
			Metod for initializing the theorems from filename into 
			some string we can pass as prolog-parameter (prolog dictionary). 
		'''
		theorems = {}

		def init_theorem(row):
			'''
				Inits a single theorem
			'''
			conclusion = row[CONCLUSION]
			assumptions = (list(row.dropna()
						  .filter(regex = f"^{ASSUMPTION}").values))
			assumptions = PL_Interface().list_to_datastring(assumptions)
			theorems[row.name] = f"({assumptions} {DERIVATION} {conclusion})"

		df = pd.read_csv(filename, index_col="Name")
		df.apply(init_theorem, axis=1)
		self.test = PL_Interface().list_to_datastring(list(theorems.values()))
		
		return f"theorems{PL_Interface().dict_to_datastring(theorems)}"

	def proofed(self):
		'''
			Checks, if theorem is proofed.
		'''
		return true

	def proof(self):
		'''
			Core function for proving [self.assumptions] ⊦ self.conclusion.
		'''
		def get_rules(assumptions, conclusion):
			'''
				Returns a python dictionary of all the rules which can applied to deduce 
				the "conclusion" from the "assumptions". Key is the rule name from the 
				file which contains all the rules, and value is the rule itself in form of 
				some derivation. 
			'''

			derivation = (f"{PL_Interface().list_to_datastring(self.assumptions)} {DERIVATION} {self.conclusion}")
			print(derivation)
			print(self.test)
			result = PL.query(f"usable_theorems_dict({derivation}, {self.theorems}, Z)")
			result2 = PL.query(f"usable_theorems({derivation}, {self.test}, Z)")
			print(result)
			result = PL_Interface().swipl_to_rules(result[0]['Z'])
			return result

		possible_rules = get_rules(self.assumptions, self.conclusion)

		for key in possible_rules:
			self.network.connect_rule(key, possible_rules[key])

		#if(proofed)
	


p = Proof(["(p→(q→r))", "(p→q)", "p"], "r")
p.proof()
p.network.draw()
#p.show_graph(p.graph.graph)