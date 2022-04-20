from tkinter import *
from tkinter import ttk

import pandas as pd

from collections import deque

class ShiftControl(Frame):
    def __init__(self, parent_shift, parent_shifted, apply_method, dataset):
        Frame.__init__(self, parent_shift)
        Frame.__init__(self, parent_shifted)
        
        self.max = len(dataset)
        self.index_pool = deque(range(self.max))
        self.parent = parent_shift
        self.parent2 = parent_shifted

        self.apply = apply_method
        self.data = dataset

        self.backward = Button(self.parent, text="◀", command = self.backward)
        self.backward.grid(column=0, row=0,  sticky='news')

        self.forward = Button(self.parent, text="▶", command = self.forward)
        self.forward.grid(column=1, row=0,  sticky='news')   

        self.inner = Label(self.parent, text=self.get_label_text("Proof"))
        self.inner.grid(column=2, row=0, stick='w')

        self.switch_frame = Frame(self.parent2)
        self.switch_frame.grid(column=0, row=1, columnspan=3)
        self.apply(self.switch_frame, self.data[0])

    def get_label_text(self, switch_name):
        return f"{switch_name} {self.index_pool[0] + 1} from {self.max}"


    def switch(self, steps):
        ###
        # Table 
        ###
        self.switch_frame.destroy()
        self.switch_frame = Frame(self.parent2)
        self.switch_frame.grid(column=0, row=1, columnspan=3)
        self.index_pool.rotate(steps)

        self.inner["text"] = self.get_label_text("Proof")
        self.apply(self.switch_frame, self.data[self.index_pool[0]])
        #tbl = ProofTable(self.table_frame, data[self.index_pool[0]])
    
    def forward(self):
        self.switch(1)
    def backward(self):
        self.switch(-1)



    
def init_table(parent_frame, table):
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


test1 = {'Assumptions': {1: {1}, 2: {2}, 3: {3}, 4: {4}, 5: {3, 4}, 6: {3}, 7: {1, 3}, 8: {1, 2, 3}, 9: {1, 2}}, 'Index': {1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9}, 'Proposition': {1: 'p→q', 2: '¬q', 3: '¬ (¬p)', 4: '¬p', 5: '¬p∧ ¬ (¬p)', 6: 'p', 7: 'q', 8: 'q∧ ¬q', 9: '¬p'}, 'Premisses': {1: set(), 2: set(), 3: set(), 4: set(), 5: {3, 4}, 6: {4, 5}, 7: {1, 6}, 8: {2, 7}, 9: {8, 3}}, 'Rule': {1: 'A', 2: 'A', 3: 'A', 4: 'A', 5: '∧I', 6: '¬E', 7: '→E', 8: '∧I', 9: '¬E'}}
test2 = {'Assumptions': {1: {1}, 2: {2}, 3: {3}, 4: {1, 3}, 5: {1, 2, 3}, 6: {1, 2}}, 'Index': {1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6}, 'Proposition': {1: 'p→q', 2: '¬q', 3: 'p', 4: 'q', 5: 'q∧ ¬q', 6: '¬p'}, 'Premisses': {1: set(), 2: set(), 3: set(), 4: {1, 3}, 5: {2, 4}, 6: {3, 5}}, 'Rule': {1: 'A', 2: 'A', 3: 'A', 4: '→E', 5: '∧I', 6: '¬I'}}
data = []

data.append(pd.DataFrame(test1))
data.append(pd.DataFrame(test2))
print(data[0])
print(data[1])


root = Tk()

shift_frame = Frame(root)
shift_frame.grid(column=0, row=0, sticky='w')

shifted_frame = Frame(root)
shifted_frame.grid(column=0, row=1, sticky='w')

shift = ShiftControl(shift_frame, shifted_frame, init_table, data)


root.mainloop()