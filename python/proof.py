
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
		self.original = None
		self.proof_derivations = None
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
		self.derivation = f"([{','.join(self.assumptions)}],[]) ⊢ {self.conclusion}"

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
			self.proof_derivations = self.init_debug()
			self.tables = self.init_tables()
			self.graphs = self.init_graphs()


	def print_all_debug(self):
		ln = len(self.proof_derivations)
		for i in range(ln):
			print(f"Proof {i+1} from {ln}:")
			self.print_debug(i)
			print()

	def print_debug(self, i):
		'''
			For printing some debug dictionary of form {key: value} in form key : value, where every (key, value) pair is in seperate line.
		'''
		debug = self.proof_derivations[i]

		for key, value in debug.items():
			print(key, ' : ', value)


	def init_debug(self):
		def conclude(index, inner, df):
			'''
				Returns the derivation sequence of some line in proof table.
			'''
			def get_parameter(name, function):
				'''
					Gets the parameter p of some function of type f(p).
				'''
				inner = function.removeprefix(name)[1:-1]
				if(inner == ''):	
					return []
				elif inner[0] == '[':
					return inner[1:-1]
				else: 
					return inner
			'''
				Body of function conclude
			'''		

			d0 = d1 = rule = step = "" 

			for entry in inner:
				if entry.startswith("d0"):
					d0 = get_parameter("d0", entry)
				elif entry.startswith("d1"):
					d1 = get_parameter("d1", entry)
				elif entry.startswith("rule"): 
					rule = get_parameter("rule", entry)
				elif entry.startswith("step"):					
					step = get_parameter("step", entry)

			line = {'Index':index,
					'LastConclusion': d0,
					'NextConclusion': d1,
					'Rule': rule,
					'Step': step}
			return pd.DataFrame([line])

		def is_unique_value(dictionary, key, value):
			to_append = True
			for index in dictionary:
				if dictionary[index].equals(value):
					to_append = False

			return to_append

		def derivation_table_to_dict(table):
			'''
				converts a derivation table with columns Index, LastConclusion, NextConclusion, Rule, Step in some 
				dict with 
				case 1: value same as LastConclusion
					Index same as column Index 
					Dict position same as column Step
				case 2: value same as NextConclusion and NextConclusion is not equal to LastConclusion
					Index same as column Index minus 0.5
					Dict position same as column Step, but lower than LastConclusion
			'''
			dct = []
			for prf in table.values():
				res = {}
				ln = len(prf)
				
				nxt = None
				for i in range(1, ln + 1):
					row = prf.loc[prf['Step'] == f'{i}']
					if row['LastConclusion'].tolist()[0] != '':
						lst = row['LastConclusion'].tolist()[0]

						if nxt != None:
							if i > 1 and lst != nxt and nxt != '':
								d = idx - 0.5
								res[d] = nxt


						idx = row['Index'].tolist()[0]
						
						if lst != '': 
							res[idx] = lst



						nxt = row['NextConclusion'].tolist()[0]

						if i == ln and nxt != '':
							d = idx - 0.5
							res[d] = nxt
				dct.append(res)

			return dct



		def main():
			'''
				Function init_tables(self) is called from here
			'''
			table = {}
			i = 0
			for proof in self.original:
				df = pd.DataFrame(
						   columns=['Index', 'LastConclusion', 'NextConclusion', 'Rule', 'Step'])

				for key in proof:
					new_frame = [df, conclude(key, proof[key], df)]
					df = pd.concat(new_frame)	

				df.index = df['Index'] # sets key

				#if is_unique_value(table, i, df):
				table[i] = df
				i = i + 1

			return derivation_table_to_dict(table)
		
		# Body of function init_debug(self)
		return main()

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

		def conclude(index, inner, df, debug):
			'''
				Returns some conclusion line different frome assumption line in table.
			'''
			def get_parameters(name, function):
				'''
					Gets the parameters [a1, a2, ..., an] in form of a list
					of some function of type f1(a1, a2, ..., an).
				'''
				inner = function.removeprefix(name)[2:-2]
				inner = inner.split(",")
				if(inner[0] == ''):	
					return []
				else: 
					return inner
			'''
				Body of function conclude
			'''
			premisses_origin = set([]) 		# premiss parameter in table (column 3). Collect all premisses with origin in assumptions.
			premisses_no_origin = set([])	# premiss parameter in table (column 3). Collect all premisses with no origin in assumptions.
			premisses_exc_origin = set([])  # premiss parameter in table (column 3). Collect all premisses with origins to be removed. 
			assumptions = set([]) 			# assumption parameter in table (column 0) (includes ex, which must be seperately eliminated)
			#origin = set([]) 				# possible assumptions from prolog output
			#ex = set([]) 					# propositions which are eliminated from assumptions
			rule = "" 						# rule name
			conclusion = "" 				# proposition name

			for entry in inner:
				if entry.startswith("assumptions"):
					assumptions = get_parameters("assumptions", entry)
				elif entry.startswith("premisses_origin"):
					premisses_origin = get_parameters("premisses_origin", entry)
				elif entry.startswith("premisses_no_origin"):
					premisses_no_origin = get_parameters("premisses_no_origin", entry)
				elif entry.startswith("premisses_exc_origin"):
					premisses_exc_origin = get_parameters("premisses_exc_origin", entry)
				elif entry.startswith("conclusion"): 
					conclusion = get_parameters("conclusion", entry)[0]
				elif entry.startswith("rule"): 
					rule = get_parameters("rule", entry)[0]					

			idx_all_assumptions = set([])
			idx_assumptions = set([])
			idx_exc_assumptions = set([])
			idx_premisses_origin = set([]) 
			idx_premisses_no_origin = set([])
			idx_premisses_exc_origin = set([])
			idx_premisses = set([])

			try:
				idx_all_assumptions = set([df.loc[(df['Proposition'] == assumption) &
									  (df['Rule'] == 'A')]["Index"].item() 
									  		for assumption in assumptions])
			except:
				print(f"Assumptions: {assumptions}")
				print(f"Table at moment: {df}")
				print(f"Development of derivations: ")
				self.print_debug(debug)
				raise ValueError('Could not locate assumptions in a right way.')



			for premiss in premisses_origin:
				select = df.loc[(df['Proposition'] == premiss) & 
								(df['Assumptions'].apply(lambda x: x.issubset(idx_all_assumptions)))]
				try:
					idx_premisses_origin = idx_premisses_origin.union(set([select["Index"].item()]))
					idx_assumptions = idx_assumptions.union(select["Assumptions"].item())
				except:
					print(f"At derivation: {self.derivation}")
					print(f"Table at moment: {df}")
					print(f"Selection: {select}")
					print(f"Indexes of most possible assumptions: {idx_all_assumptions}")
					print(f"Premiss to append on table: {premiss}")
					print(f"Development of derivations: ")
					self.print_debug(debug)
					raise ValueError('Proof table could not be created. The last index occurs at least 2 times in the previous propositions.')		

			for premiss in premisses_no_origin:
				select = df.loc[(df['Proposition'] == premiss)]
				try:
					idx_premisses_origin = idx_premisses_origin.union(set([select["Index"].item()]))
				except:
					print(f"At derivation: {self.derivation}")
					print(f"Table at moment: {df}")
					print(f"Selection: {select}")
					print(f"Indexes of most possible assumptions: {idx_all_assumptions}")
					print(f"Premiss to append on table: {premiss}")
					print(f"Development of derivations: ")
					self.print_debug(debug)
					raise ValueError('Proof table could not be created. The last index occurs at least 2 times in the previous propositions.')		


			for premiss in premisses_exc_origin:
				select = df.loc[(df['Proposition'] == premiss) & 
								(df['Assumptions'].apply(lambda x: x.issubset(idx_all_assumptions)))]
				try:
					idx_premisses_exc_origin = idx_premisses_exc_origin.union(set([select["Index"].item()]))
					idx_exc_assumptions = idx_exc_assumptions.union(select["Assumptions"].item())
				except:
					print(f"At derivation: {self.derivation}")
					print(f"Table at moment: {df}")
					print(f"Selection: {select}")
					print(f"Indexes of most possible assumptions: {idx_all_assumptions}")
					print(f"Premiss to append on table: {premiss}")
					print(f"Development of derivations: ")
					self.print_debug(debug)
					raise ValueError('Proof table could not be created. The last index occurs at least 2 times in the previous propositions.')		

			idx_premisses = idx_premisses_origin.union(idx_premisses_no_origin)

			line = {'Assumptions': idx_assumptions.difference(idx_exc_assumptions),
					'Index': index,
					'Proposition': conclusion,
					'Premisses': idx_premisses,
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
					if len(proof[key]) == 2: # assumptions have two elements
						new_frame = [df, assume(key, proof[key][0])]
					else: # general conclusions have more than two elements 
						new_frame = [df, conclude(key, proof[key], df, i)]
					df = pd.concat(new_frame)	

				df.index = df['Index'] # sets key

				#if is_unique_value(table, i, df):
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
	p.view_graph(1)


# MTT
# assumptions = ["(p→q)", "¬(q)"]
# conclusion = "¬(p)"
#