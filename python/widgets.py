from tkinter import *
import re
from itertools import cycle, islice, dropwhile



class FormulaEditor(Toplevel):
	#SQUARES = '▯▮'
	def __init__(self, master = None):
		super().__init__(master = master)
		self.title('Tkalc')

		self.disp = Label(window, text='▮')
		self.disp.grid(column=0, row=0, columnspan=5)

		keys = '-+<C¬∧∨→pqrs'
		self.bt_list = [self.bt_draw(keys[n], n%4, n//4) for n in range(12)]

	def replace_section(self, text):
		'''
			Replaces propositions like (p ∧ ▮) ∨ q with (▮ ∨ q), means the smallest subproposition 
			which has ▮ is replaced by ▮ itself
		'''
		def match(text, idx, reverse=False):
			'''
				If idx is the index of a bracket ')' (reverse=True) or '(' (reverse=False), 
				the algorithm searchs the corresponding index idy for the bracket 
				'(' or ')', such that text[idx:idy] is a proposition. 
			'''
			if reverse == True: text = text[::-1]
			stack = []
			for index1, char in enumerate(text):
				if char == '(':
					# put every `(` on stack (or rather its index)
					stack.append( index1 )
				elif char == ')':
					# get `(` for current `)
					index2 = stack.pop(-1)
					if index1 == idx or index2 == idx:
						if reverse == False:
							return index1, index2
						else:
							n = len(text)
							return (n - index1), (n - index2)
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
				print(index1, index2)
				text = text[:index2] + '▮' + text[index1+1:]
			else:
				index = text.find('▮)') 

				if index != -1: # of form ▮)
					reverse_text = invert(text)
					n = len(reverse_text)
					index = n - index - 2
					index1, index2 = match(reverse_text, index)
					index1 = n - index1 - 1
					index2 = n - index2 - 1
					text = text[:index1] + '▮' + text[index2+1:]
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
	    self.bt = Button(window, text=key, command=lambda: self.bt_press(key))
	    self.bt.grid(column=col+1, row=lin+1)
	    return self.bt

	def bt_press(self, key):
	    if   key == 'C': self.disp['text'] = '▮'
	    elif key == '<': self.disp['text'] = self.replace_section(self.disp['text'])
	    elif key in ['∧', '∨', '→']: self.disp['text'] = self.disp['text'].replace('▮', f'(▮{key}▯)')
	    elif key == '¬': self.disp['text'] = self.disp['text'].replace('▮', '(¬▮)')
	    elif key == '+': self.disp['text'] = self.switch(1, '▯', self.disp['text'])
	    elif key == '-': self.disp['text'] = self.switch(-1, '▯', self.disp['text'])
	    else           : self.disp['text'] = self.switch(1, key, self.disp['text'])

window = Tk()

a = FormulaEditor(window)

window.mainloop()