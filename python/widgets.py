from tkinter import *
from tkinter import ttk

from config import *
import re
from itertools import cycle, islice, dropwhile

from anytree import Node, PreOrderIter

from proof import *

class PropositionEditor(Toplevel):
	#SQUARES = '▯▮'
	def __init__(self, master = None, apply_method=None):
		super().__init__(master = master)
		self.title('PropositionEditor')
		self.apply = apply_method

		self.disp = Label(self, text='▮')
		self.disp.grid(column=0, row=0, columnspan=4)

		keys = '-+<C¬∧∨→pqrs✔'
		self.bt_list = [self.bt_draw(keys[n], n%4, n//4) for n in range(13)]

	def replace_section(self, text):
		'''
			Replaces propositions like (p ∧ ▮) ∨ q with (▮ ∨ q), means the smallest subproposition 
			which has ▮ is replaced by ▮ itself
		'''
		def match(text, idx):
			'''
				If idx is the index of a bracket '(', 
				the algorithm searchs the corresponding index idy for the bracket 
				')', such that text[idx:idy] is a proposition. 
			'''
			stack = []
			for index1, char in enumerate(text):
				if char == '(':
					# put every `(` on stack (or rather its index)
					stack.append( index1 )
				elif char == ')':
					# get `(` for current `)
					index2 = stack.pop(-1)
					if index1 == idx or index2 == idx:
							return index1, index2
		def reverse_match(text, idx):
			'''
				If idx is the index of a bracket ')', 
				the algorithm searchs the corresponding index idy for the bracket 
				'(', such that text[idx:idy] is a proposition. 
			'''
			reverse_text = invert(text)
			n = len(reverse_text)
			idx = n - idx - 2
			index1, index2 = match(reverse_text, idx)
			index1 = n - index1 - 1
			index2 = n - index2 - 1
			return index2, index1
		def invert(text):
			'''
				Reverses the string 'text' and transposes '(' and ')' in that, so that match function can 
				be applied.
			'''
			reverse_text = text[::-1]
			reverse_text = reverse_text.replace('(', '#')
			reverse_text = reverse_text.replace(')', '(')
			reverse_text = reverse_text.replace('#', ')')
			return reverse_text

		index_full_rect = text.find('▮')
		if index_full_rect == -1: text = '▮'

		index_neg = text.find('(¬▮)')
		if index_neg != -1: # of form (¬▮)
			text = text.replace('(¬▮)','▮')
		else: 
			index = text.find('(▮') # of form (▮
			if index != -1:
				index1, index2 = match(text, index)
				text = text[:index2] + '▮' + text[index1+1:]
			else:
				index = text.find('▮)') 

				if index != -1: # of form ▮)
					index1, index2 = reverse_match(text, index)
					print(index1,index2)
					text = text[:index2] + '▮' + text[index1+1:]
		return text


	def switch(self, step, elem, text):
		'''
			Moves the cursor ▮ a count of 'step' steps accross ▯-elements.
			Example (▮∧(▯→▯)) with step = 1 gives (▯∧(▮→▯)) and with step = -1 
			gives (▯∧(▯→▮))
		'''
		sign = (step <= 0)
		step = abs(step)

		indices_empty_rect = [i.start() for i in re.finditer('▯', text)]
		index_full_rect = text.find('▮')

		if index_full_rect == -1: return text
		indices_empty_rect.append(index_full_rect)
		indices_empty_rect.sort(reverse=sign)

		cycled = cycle(indices_empty_rect)
		skipped = dropwhile(lambda x: x != index_full_rect, cycled) 
		sliced = islice(skipped, None, step + 1)

		result = list(sliced)
		reset_to_full_rect = result[-1]
		if elem == '▯':
			text = text[:index_full_rect] + elem + text[index_full_rect + 1:]
			text = text[:reset_to_full_rect] + '▮' + text[reset_to_full_rect + 1:]
		else:
			text = text[:reset_to_full_rect] + '▮' + text[reset_to_full_rect + 1:]	
			text = text[:index_full_rect] + elem + text[index_full_rect + 1:]
		return text

	def bt_draw(self, key, col, lin):
	    self.bt = Button(self, text=key, command=lambda: self.bt_press(key))
	    self.bt.grid(column=col, row=lin+1, sticky='nesw')
	    return self.bt



	def bt_press(self, key):
		if   key == 'C': self.disp['text'] = '▮'
		elif key == '<': self.disp['text'] = self.replace_section(self.disp['text'])
		elif key in ['∧', '∨', '→']: self.disp['text'] = self.disp['text'].replace('▮', f'(▮{key}▯)')
		elif key == '¬': self.disp['text'] = self.disp['text'].replace('▮', '(¬▮)')
		elif key == '+': self.disp['text'] = self.switch(1, '▯', self.disp['text'])
		elif key == '-': self.disp['text'] = self.switch(-1, '▯', self.disp['text'])
		elif key == '✔': self.apply(self.disp['text']), self.destroy()
		else           : self.disp['text'] = self.switch(1, key, self.disp['text'])



class ProofTable(Toplevel):
	def __init__(self, master = None, table=None, derivation=None):
		super().__init__(master = master)
		self.table = table
		self.derivation = derivation
		self.title('ProofTable')

		self.init_table()
	
	def init_table(self):

		lbl = Label(self, text=self.derivation)
		lbl.grid(column=0, row=0, columnspan=5)

		for index in self.table.index:
			# Assumptions
			s_assumptions = ', '.join([str(s) for s in self.table["Assumptions"][index]])
			lbl = Label(self, text=s_assumptions)
			lbl.grid(column=0, row=index+1, sticky='e')

			# Index
			lbl = Label(self, text=self.table["Index"][index])
			lbl.grid(column=1, row=index+1, sticky='e')

			# Proposition
			lbl = Label(self, text=self.table["Proposition"][index])
			lbl.grid(column=2, row=index+1, sticky='w')

			# Premisses
			s_premisses = ', '.join([str(s) for s in self.table["Premisses"][index]])

			lbl = Label(self, text= s_premisses)
			lbl.grid(column=3, row=index+1, sticky='e')

			# Rule
			lbl = Label(self, text= self.table['Rule'][index])
			lbl.grid(column=4, row=index+1, sticky='w')



class DerivationTool(Frame):
	def __init__(self, parent, apply_assumption=None, apply_conclusion=None):
		Frame.__init__(self, parent)

		self.parent = parent
		self.apply_assumption = apply_assumption
		self.apply_conclusion = apply_conclusion

		self.bt_new_assumption = Button(self.parent, text="Add Assumption", command=lambda: self.new_FormulaEditor(self.apply_assumption))
		self.bt_new_assumption.grid(column=0, row=1)

		self.bt_new_conclusion = Button(self.parent, text="Add Conclusion", command=lambda: self.new_FormulaEditor(self.apply_conclusion))
		self.bt_new_conclusion.grid(column=1, row=1)


	def get_derivation(self):
		'''
			Gets the derivation-string from the Table generated by functions 
			apply_assumption and apply_conclusion.
		'''
		assumptions = []
		conclusion = ""
		derivation = ""

		for child in self.parent.grid_slaves(column=0):
			g_info = child.grid_info()
			if type(child) is Label:
				assumptions.append(child['text'])

		
		for child in self.parent.grid_slaves(column=1):
			g_info = child.grid_info()
			if type(child) is Label:
				conclusion = child['text']

		if conclusion != "":
			derivation = f"([{','.join(assumptions)}],[])⊦{conclusion}"

		return derivation

	def new_FormulaEditor(self, apply):	
		'''
			Opens a new PropositionEditor window with custom apply function.
		'''
		PropositionEditor(self.parent, apply)

class Derivation(Frame):
	def __init__(self, parent):
		Frame.__init__(self, parent)
		self.parent = parent

		self.main_frame = Frame(self.parent)
		self.main_frame.grid(column=0, row=0)

		self.init_main_frame()


	
	def init_main_frame(self):
		self.toolbar = Frame(self.main_frame)
		self.toolbar.grid(column=0,row=0, sticky='w')

		self.i_calc = PhotoImage(file=I_QED)
		self.calc = Button(self.toolbar, image=self.i_calc, bg='white', command=self.proof)
		self.calc.grid(column=0, row=0)
		self.calc.configure(state=DISABLED)

		self.i_graph = PhotoImage(file=I_GRAPH)
		self.bt_graph = Button(self.toolbar, image=self.i_graph, bg='lightblue', command=self.graph)
		self.bt_graph.grid(column=1, row=0)
		self.bt_graph.configure(state=DISABLED)

		self.i_tbl = PhotoImage(file=I_TBL)
		self.tbl = Button(self.toolbar, image=self.i_tbl, bg='lightgreen', command=self.proofTable)
		self.tbl.grid(column=2, row=0)
		self.tbl.configure(state=DISABLED)

		self.i_reset = PhotoImage(file=I_RESET)
		self.reset = Button(self.toolbar, image=self.i_reset, bg='white', command=self.reset)
		self.reset.grid(column=3, row=0)

		self.derivation = DerivationTool(self.main_frame, self.apply_assumption, self.apply_conclusion)


	def proof(self):
		'''
			Generates a proof of the derivation by natural deduction.
		'''
		self.calc.configure(state=DISABLED)
		self.derivation.bt_new_assumption.configure(state=DISABLED)
		self.bt_graph.configure(state=NORMAL)
		self.tbl.configure(state=NORMAL)

		derivation = self.derivation.get_derivation()
		self.proof = Proof(derivation)
		self.proof.proof()

		if GET_PROTOCOLL == True:
			atv = AnyTreeView(root, self.proof.derivation_tree)
			atv.generate()


	def graph(self):
		'''
			Draws some networkx-graph illustrates the proof.
		'''
		self.proof.view_graph(0)

	def proofTable(self):
		derivation = self.proof.derivation

		ProofTable(root, self.proof.tables[1], derivation)

	def reset(self):
		# destroy all widgets from frame
		for widget in self.main_frame.winfo_children():
			widget.destroy()

		self.main_frame.destroy()
    
		# this will clear frame and frame will be empty
		# if you want to hide the empty panel then

		self = Derivation(self.parent)


	def apply_assumption(self, lbl_txt):
		row = len(self.main_frame.grid_slaves(column=0))+1
		lbl = Label(self.main_frame, text=lbl_txt)
		lbl.grid(row=row, column=0)

	def apply_conclusion(self, lbl_txt):
		row = len(self.main_frame.grid_slaves(column=1))+1
		lbl = Label(self.main_frame, text=lbl_txt)
		lbl.grid(row=row, column=1)
		self.derivation.bt_new_conclusion.configure(state=DISABLED)
		self.calc.configure(state=NORMAL)


class AnyTreeView(Toplevel):
	'''
		Illustrates some anytree treeview into some 
	'''
	def __init__(self, master, tree ):	
		super().__init__(master = master)
		
		self.main_frame = Frame(self)
		self.main_frame.grid(row=1,column=1,sticky="ew")
		self.columnconfigure(1, weight=1)


		self.title('AnyTreeView')
		
		self.tree = tree
		h = len([node.name for node in PreOrderIter(tree)])
		self.treeview = ttk.Treeview(self.main_frame, column=("c1"), height = h)
		self.treeview.column("# 1",anchor=CENTER, stretch=YES)

		# Streching treeview after right atjust the window
		self.columnconfigure(1, weight=1)
		self.treeview.pack(expand=True, fill='x')

	def generate(self):

		def separate_string(data, seps):
			'''
				Separates strings by seperators constist of more than one char saved in the variable seps.
				Receive the last separated string s1 and the last separator which has s1 on his right hand side.
				https://stackoverflow.com/questions/71630052/python-separate-string-by-multiple-separators-and-return-separators-and-separat
			'''
			import re

			pattern = "|".join(re.escape(sep) for sep in seps)
			try:
				start, end = [m.span() for m in re.finditer(pattern, data)][-1]
				return f"{data[start:end]},{data[end:]}"
			except IndexError:
				return data
		

		index = 0
		for node in PreOrderIter(self.tree):
			print(node.name)
			self.treeview.insert('',f'{index}', node.name, text = separate_string(node.name, BASIC_RULES.values()))
			index = index + 1

		for node in PreOrderIter(self.tree):
			for child in node.children:
				self.treeview.move(child.name, node.name, 'end')




root = Tk()


derivation = Derivation(root)

root.mainloop()