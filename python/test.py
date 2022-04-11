from tkinter import *
from tkinter import ttk

from anytree import Node, RenderTree, AsciiStyle, PreOrderIter

# anytree definition
udo = Node("Udo the very first king of London and Manchester, born in China and studied in Japan.")
marc = Node("Marc the second monarch of south carolina married Isabel the very first arab princess.", parent=udo)

class AnyTreeView(Toplevel):
    '''
        Illustrates some anytree treeview into some 
    '''
    def __init__(self, master, tree ):  
        super().__init__(master = master)

        self.resizable(width=True, height=False)
        
        self.main_frame = Frame(self)
        self.main_frame.grid(row=1,column=1,sticky="ew")


        self.title('AnyTreeView')
        
        self.tree = tree
        h = len([node.name for node in PreOrderIter(tree)])
        self.treeview = ttk.Treeview(self.main_frame, column=("c1"), height = h)
        self.treeview.column("# 1",anchor=CENTER, stretch=YES)


        # Streching treeview after right atjust the window
        self.columnconfigure(1, weight=1)
        self.treeview.pack(expand=True, fill='x')


    def generate(self):
        '''
        Dynamically generates the treeview object with the nodes from the parameter tree.
        '''

        index = 0
        for node in PreOrderIter(self.tree):
            print(node.name)
            self.treeview.insert('',f'{index}', node.name, text = node.name)
            index = index + 1

        for node in PreOrderIter(self.tree):
            for child in node.children:
                self.treeview.move(child.name, node.name, 'end')

def m_tree():
    tv = AnyTreeView(root, udo)
    tv.generate()

root = Tk()

bt = Button(text ="Tree", command = m_tree)
bt.pack()

root.mainloop()