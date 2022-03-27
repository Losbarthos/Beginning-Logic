from tkinter import *
from tkinter import ttk

from anytree import Node, RenderTree, AsciiStyle, PreOrderIter

# anytree definition
udo = Node("Udo the very first king of London and Manchester, born in China and studied in Japan.")
marc = Node("Marc the second monarch of south carolina married Isabel the very first arab princess.", parent=udo)

print(udo.name)

udo.name = "udo"

print(udo.name)