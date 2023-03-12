#!/usr/bin/env python

#  Basic libary to prove theorems
#    Author:        Martin Kunze
#    E-mail:        mkunze86@gmail.com
#    Copyright (c)  2022, Martin Kunze

from config import *
from proof import *


from tkinter import *
from tkinter import ttk
from tkinter.ttk import Progressbar

import matplotlib
import matplotlib.pyplot as plt
matplotlib.use('GTK3Agg')

import re
from itertools import cycle, islice, dropwhile
from collections import deque

import pandas as pd

class ProgressBarWindow(Toplevel):
	def __init__(self, master = None, max_value=None):
		super().__init__(master = master)
		self.protocol("WM_DELETE_WINDOW", self.nothing)

		self.title('ProgressBar')
		self.size = max_value
		self.step = 0
		
		##
		# ProgressBar
		##
		self.prog_bar = Progressbar(self, orient=HORIZONTAL, mode='determinate')
		self.prog_bar.grid(column=0, row=0)

		self.lbl = Label(self) 
		self.lbl.grid(column=1,row=0)

	def nothing(self):
		"dummy function"
		pass
	
	def quit(self):
		self.destroy()

	def update(self):
		'''
			Gets one step further in progress bar.
		'''
		self.step = self.step + 1
		current_value = self.prog_bar['value']
		prog_length =  int(self.prog_bar['length'].string)

		self.prog_bar['value'] = current_value + prog_length / self.size 

		self.lbl['text'] = f'{self.step} from {self.size}'
		self.update_idletasks()

class PropositionEditor(Toplevel):
	#SQUARES = '▯▮'
	def __init__(self, master = None, apply_method=None):
		super().__init__(master = master)
		self.title('PropositionEditor')
		self.apply = apply_method

		self.disp = Label(self, text='▮')
		self.disp.grid(column=0, row=0, columnspan=4)

		keys = '-+<C∧∨→↔¬pqrs✔'
		self.bt_list = [self.bt_draw(keys[n], n%4, n//4) for n in range(len(keys))]

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
		elif key in ['∧', '∨', '→', '↔']: self.disp['text'] = self.disp['text'].replace('▮', f'(▮{key}▯)')
		elif key == '¬': self.disp['text'] = self.disp['text'].replace('▮', '(¬▮)')
		elif key == '+': self.disp['text'] = self.switch(1, '▯', self.disp['text'])
		elif key == '-': self.disp['text'] = self.switch(-1, '▯', self.disp['text'])
		elif key == '✔': self.apply(self.disp['text']), self.destroy()
		else           : self.disp['text'] = self.switch(1, key, self.disp['text'])


class ShiftControl(Frame):
    def __init__(self, parent, parent_child, apply_method, dataset, label_key_text):
        Frame.__init__(self, parent)
        Frame.__init__(self, parent_child)
        
        self.max = len(dataset)
        self.index_pool = deque(range(self.max))
        self.parent = parent
        self.parent_child = parent_child
        self.apply = apply_method
        self.data = dataset
        self.label_key_text = label_key_text

        self.backward = Button(self.parent, text="◀", command = self.backward)
        self.backward.grid(column=0, row=0,  sticky='w')
        
        self.forward = Button(self.parent, text="▶", command = self.forward)
        self.forward.grid(column=1, row=0,  sticky='w')   

        self.inner = Label(self.parent, text=self.get_label_text(self.label_key_text))
        self.inner.grid(column=2, row=0, stick='news')

        self.switch_frame = Frame(self.parent_child)
        self.switch_frame.grid(column=0, row=1, columnspan=3, sticky='news')
        self.apply(self.switch_frame, self.data[0])

    def append_data(self, element):
    	'''
    		Appends a new element to the dataset of the switch datacollection element.
    	'''
    	# Element has form deque([m, m+1, ..., n, 0, 1, ..., m-1]),
    	# Step 1: bring deque with a negative rotation of m to form deque([0, 1, m, m+1, ..., n]),    	 
    	neg_rotate = self.index_pool[0] - self.max # needet shift of deque to perform step 1.
    	self.index_pool.rotate(neg_rotate)
    	# Step 2: append n+1 to the deque, it as now the form deque([0, 1, m, m+1, ..., n, n+1]).
    	self.index_pool.append(self.max)
    	# Step 3: rotate the element again to get the origin position of the deque. It is now of form:
    	# 							deque([m, m+1, ..., n, n+1, 0, 1, ..., m-1]).
    	self.index_pool.rotate(-neg_rotate + 1)
    	self.max = self.max + 1
    	self.inner["text"] = self.get_label_text(self.label_key_text)
    	self.data[self.max - 1] = element

    def get_label_text(self, switch_name):
        return f"{switch_name} {self.index_pool[0] + 1} from {self.max}"


    def switch(self, steps):
        '''
        	Switch the values of the ShiftControl by steps. In special we only need the cases 
        	switch(1) and switch(-1) in this control element.
        '''
        for widget in self.switch_frame.winfo_children():
        	widget.destroy()

        self.switch_frame.destroy()
        self.switch_frame = Frame(self.parent_child)
        self.switch_frame.grid(column=0, row=1, columnspan=3)
        
        self.index_pool.rotate(steps)

        self.apply(self.switch_frame, self.data[self.index_pool[0]])
        self.inner["text"] = self.get_label_text(self.label_key_text)
    
    def forward(self): 
    	'''
    		performs a shift of following form:
    		deque([0, 1,..., n-1]) --> deque([1, 2, ..., n, 0])
    		so the second element is now focused. 
    	'''        
    	self.switch(-1)
    def backward(self):
    	'''
    		performs a shift of following form:
    		deque([0, 1,..., n-1]) --> deque([n, 0, 1, ..., n-1])
    		so the last element n is now focused.
    	'''
    	self.switch(1)


class Derivation(Frame):
	def __init__(self, parent):
		Frame.__init__(self, parent)
		self.parent = parent

		self.main_frame = Frame(self.parent)
		self.main_frame.grid(column=0, row=0)
		self.p = [Proof()]

		self.table = None

		self.init_main_frame()
	
	def init_main_frame(self):
		##
		#  Toolbar
		##
		self.toolbar = Frame(self.main_frame)
		self.toolbar.grid(column=0,row=0, sticky='w')

		self.i_calc = PhotoImage(file=I_QED)
		self.bt_calc = Button(self.toolbar, image=self.i_calc, bg='white', command=self.proof)
		self.bt_calc.grid(column=0, row=0)
		self.bt_calc.configure(state=DISABLED)


		self.i_calc_all = PhotoImage(file=I_QED_ALL)
		self.bt_calc_all = Button(self.toolbar, image=self.i_calc_all, bg='white', command=self.proof_all)
		self.bt_calc_all.grid(column=1, row=0)
		self.bt_calc_all.configure(state=DISABLED)

		self.i_graph = PhotoImage(file=I_GRAPH)
		self.bt_graph = Button(self.toolbar, image=self.i_graph, bg='lightblue', command=self.graph)
		self.bt_graph.grid(column=2, row=0)
		self.bt_graph.configure(state=DISABLED)


		self.i_open = PhotoImage(file=I_OPEN_FILE)
		self.bt_open = Button(self.toolbar, image=self.i_open, bg='white', command=self.import_derivations)
		self.bt_open.grid(column=3, row=0)

		self.i_latex = PhotoImage(file=I_LATEX)
		self.bt_latex = Button(self.toolbar, image=self.i_latex, bg='white', command=self.to_latex)
		self.bt_latex.grid(column=4, row=0)

		self.i_reset = PhotoImage(file=I_RESET)
		self.bt_reset = Button(self.toolbar, image=self.i_reset, bg='white', command=self.reset)
		self.bt_reset.grid(column=5, row=0)
		
		##
		# Derivation representation
		##
		self.derivation_shift_frame = Frame(self.main_frame)
		self.derivation_shift_frame.grid(column=0, row=2, sticky='w')
		self.derivation_shift_child_frame = Frame(self.derivation_shift_frame)
		self.derivation_shift_child_frame.grid(column=0, row=2, columnspan=3, sticky='w')

		self.shift_derivation = ShiftControl(self.derivation_shift_frame, self.derivation_shift_child_frame, self.set_derivation, self.p, "Derivation")

		self.init_derivation_shift_frame(self.shift_derivation.switch_frame)
	def init_derivation_shift_frame(self, inner_derivation_frame):
		'''
			After press the derivation shift buttons, the screen is updated. This method does the update.
		'''

		self.bt_add_assumption = Button(inner_derivation_frame, text = "Add Assumption", command=lambda: self.new_FormulaEditor(self.apply_assumption))
		self.bt_add_assumption.grid(column=0, row=0)
		self.bt_set_conclusion = Button(inner_derivation_frame, text = "Add Conclusion", command=lambda: self.new_FormulaEditor(self.apply_conclusion))
		self.bt_set_conclusion.grid(column=1, row=0)
		self.bt_add_derivation = Button(inner_derivation_frame, text = "+", command=lambda: self.add_derivation(Proof()))
		self.bt_add_derivation.grid(column=2, row=0)

		self.lbl_derivation = Entry(inner_derivation_frame, state="readonly", justify='center')
		self.lbl_derivation.grid(column=0, row=1, columnspan=3)
			
		##
		# Shift Control for Table view
		##
		self.table_shift_frame = Frame(inner_derivation_frame)
		self.table_shift_frame.grid(column=0, row=3, columnspan=5, sticky='w')

		self.table_shift_child_frame = Frame(self.table_shift_frame)
		self.table_shift_child_frame.grid(column=0, row=1)

		self.shift = None

	def init_toolbar_state_proofed(self, proof, index):
		'''
			Setup of the toolbar under the condition of some proofed proposition.
		'''
		self.bt_calc.configure(state=DISABLED)
		self.bt_calc_all.configure(state=DISABLED)
		self.bt_add_assumption.configure(state=DISABLED)
		self.bt_set_conclusion.configure(state=DISABLED)
		if(len(proof.graphs[index][1]) > 0 or GET_PROTOCOLL == True):
			self.bt_graph.configure(state=NORMAL)
		self.shift_table = ShiftControl(self.table_shift_frame, self.table_shift_child_frame, self.init_table, proof.tables, "Proof")

	def init_toolbar_state_not_proofed(self):
		self.bt_calc.configure(state=NORMAL)
		self.bt_calc_all.configure(state=NORMAL)
		self.bt_add_assumption.configure(state=NORMAL)
		self.bt_set_conclusion.configure(state=NORMAL)
		if(GET_PROTOCOLL == False):
			self.bt_graph.configure(state=DISABLED)

	def init_toolbar_state_no_derivation(self):
		self.bt_calc.configure(state=DISABLED)
		self.bt_calc_all.configure(state=DISABLED)
		self.bt_add_assumption.configure(state=NORMAL)
		self.bt_set_conclusion.configure(state=NORMAL)
		if(GET_PROTOCOLL == False):
			self.bt_graph.configure(state=DISABLED)

	def import_derivations(self):
		def file_to_list(file_name):
			'''
				Stores the derivations of the file into some list.
			'''
			with open(file_name,'r') as f:
				listl=[]

				for line in f:
					code_line = line.split("#")[0] # removes comments
					strip_line = code_line.strip() # removes blanks 
					if strip_line != "":
						listl.append(strip_line)
				return listl

		def add_derivation(derivation):
			'''
				Adds some derivation into proof.
			'''
			new_proof = Proof()
			try:
				new_proof.set_derivation(s)

				self.add_derivation(new_proof)
			except:
				None


		from tkinter import filedialog
		from tkinter import messagebox

		file_path = filedialog.askopenfilename(initialdir=DATA_DIR)

		if(file_path != () and file_path.endswith('txt')):
			file = file_to_list(file_path)


			loop_start = True
			for s in file:
				if loop_start == True:
					loop_start = False
					if self.p[0].derivation == "":
						self.p[0].set_derivation(s)
						self.derivation_set_text(s)
					else:
						add_derivation(s)
				else:
					add_derivation(s)
		elif file_path != ():
			messagebox.showinfo("Info", "Can import .txt-files only.")
		self.init_toolbar_state_not_proofed()

	def to_latex(self):
		from tkinter import filedialog

		f = filedialog.asksaveasfile(mode='w', defaultextension=".tex", initialdir=LATEX_DIR)
		if f is None: # asksaveasfile return `None` if dialog closed with "cancel".
			return
		# header

		f.write("% !TeX TS-program = lualatex\n") 
		f.write("\\documentclass{article}\n")
		f.write("\\usepackage{booktabs}\n")
		f.write("\\usepackage{caption}\n")
		f.write("\\usepackage{unicode-math}\n")
		f.write("\\begin{document}\n")
		f.write("\\maxdeadcycles=200\n") 
		f.write("\\extrafloats{100}\n")

		fooder = "\\end{document}\n"

		for proof in self.p:
			derivation = "$" + proof.get_derivation() +"$"
			for table in proof.tables.values():
				tbl_cpy = table
				tbl_cpy['Proposition'] = "$" + tbl_cpy['Proposition'] + "$" 
				tbl_cpy['Rule'] = "$" + tbl_cpy['Rule'] + "$"
				latex_table = tbl_cpy.style.hide(axis='index').hide(axis='columns').to_latex()#index=False,header=False,escape=False)
				#df.style.apply(highlight, axis=None).hide(axis='index').hide(axis='columns')
				f.write("\\begin{table}[htbp]")
				f.write(f"\\caption*{{{derivation}}}")
				f.write(f"\\centering")
				f.write(latex_table.replace("set()","{}"))
				f.write("\\end{table}\n")

		f.write(fooder)
		f.close()
	
	def derivation_set_text(self, text):
		'''
			Resets the text of the Entry element self.lbl_derivation
		'''
		self.lbl_derivation['state'] = 'normal'
		self.lbl_derivation.delete(0, 'end')
		self.lbl_derivation.insert(0, text)
		self.lbl_derivation['state'] = 'readonly'

	def get_current_proof(self):
		'''
			Gets the current Proof variable "proof" based on some derivation and the index of the illustrated proof
			from this variable.
		'''
		index = self.shift_derivation.index_pool[0]
		proof = self.shift_derivation.data[index]

		return proof

	def set_derivation(self, parent_frame, proof):
		self.init_derivation_shift_frame(parent_frame)
		self.derivation_set_text(proof.get_derivation())
		self.lbl_derivation['width'] = 0

		if proof.is_proven(): 
			if proof.is_proven() != False: # The proof has found some valid result
				proof = self.get_current_proof()
				self.init_toolbar_state_proofed(proof, 0)
			else:
				self.init_toolbar_state_not_proofed()
		else:
			if proof.conclusion == "":
				self.init_toolbar_state_no_derivation()
			else:
				self.init_toolbar_state_not_proofed()


	def add_derivation(self, element):
		self.p.append(element)
		self.shift_derivation.append_data(element)
		#self.reset_lbl_derivation_width()


	def init_table(self, parent_frame, table):
	    for index in table.index:
	        # Assumptions
	        s_assumptions = ', '.join([str(s) for s in table["Assumptions"][index]])
	        lbl = Label(parent_frame, text=s_assumptions)
	        lbl.grid(column=0, row=index, sticky='e')

	         # Index
	        lbl = Label(parent_frame, text=f'({table["Index"][index]})')
	        lbl.grid(column=1, row=index, sticky='e')

	        # Proposition
	        lbl = Label(parent_frame, text=table["Proposition"][index])
	        lbl.grid(column=2, row=index, sticky='w')

	        # Premisses
	        s_premisses = ', '.join([str(s) for s in table["Premisses"][index]])

	        lbl = Label(parent_frame, text= s_premisses)
	        lbl.grid(column=3, row=index, sticky='e')

	        # Rule
	        lbl = Label(parent_frame, text= table['Rule'][index])
	        lbl.grid(column=4, row=index, sticky='w')

	def proof_all(self):
		'''
		 	Generates proofs of all derivations by natural deduction.
		'''
		prog_bar = ProgressBarWindow(self.parent, len(self.p))


		for proof in self.p:
			if proof.is_proven != True:
				proof.proof()
			prog_bar.update()
		
		current_proof = self.get_current_proof()
		if current_proof.is_proven() != False:
			self.init_toolbar_state_proofed(current_proof, 0)
		prog_bar.quit()



	def proof(self):
		'''
			Generates a proof of the derivation by natural deduction.
		'''
		from tkinter import messagebox
		proof = self.get_current_proof()
		proof.proof()
		
		if proof.is_proven() != False:
			self.init_toolbar_state_proofed(proof, 0)
		else:
			messagebox.showinfo("Info", "Proof failed!")


		if GET_PROTOCOLL == True:
			proof.print_all_debug()
			#atv = AnyTreeView(root, self.proof.derivation_tree)
			#atv.generate()


	def graph(self):
		'''
			Draws some networkx-graph illustrates the proof.
		'''
		from tkinter import messagebox

		proof = self.get_current_proof()
		index = self.shift_table.index_pool[0]
		if GET_PROTOCOLL == True:
			proof.view_graph_debug(index)
		else:
			proof.view_graph(index)
		

	def reset(self):
		# destroy all widgets from frame
		for widget in self.main_frame.winfo_children():
			widget.destroy()

		self.main_frame.destroy()
    
		# this will clear frame and frame will be empty
		# if you want to hide the empty panel then

		self = Derivation(self.parent)

	def new_FormulaEditor(self, apply):	
		'''
			Opens a new PropositionEditor window with custom apply function.
		'''
		PropositionEditor(self.parent, apply)

	def apply_assumption(self, lbl_txt):
		proof = self.shift_derivation.data[self.shift_derivation.index_pool[0]]
		proof.add_assumptions(lbl_txt)
		self.derivation_set_text(proof.get_derivation())

	def apply_conclusion(self, lbl_txt):
		proof = self.shift_derivation.data[self.shift_derivation.index_pool[0]]
		proof.set_conclusion(lbl_txt)
		self.derivation_set_text(proof.get_derivation())
		self.bt_calc.configure(state=NORMAL)

root = Tk()
root.title("Beginning Logic")
derivation = Derivation(root)

root.mainloop()