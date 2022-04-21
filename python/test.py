#!/usr/bin/env python
# coding: utf-8

import matplotlib.pyplot as plt
import networkx as nx

from netgraph import Graph # pip install netgraph

node_labels = {1: 'p→q', 2: '¬q', 3: '¬ (¬p)', 4: '¬p', 5: '¬p∧ ¬ (¬p)', 6: 'p', 7: 'q', 8: 'q∧ ¬q', 9: '¬p'}
color_map = {1: 'red', 2: 'red', 3: 'red', 4: 'red', 5: 'lightblue', 6: 'lightblue', 7: 'lightblue', 8: 'lightblue', 9: 'blue'}
edge_labels = {(3, 5): '∧I', (4, 5): '∧I', (4, 6): '¬E', (5, 6): '¬E', (1, 7): '→E', (6, 7): '→E', (2, 8): '∧I', (7, 8): '∧I', (8, 9): '¬E', (3, 9): '¬E'}
highlight = {1: {1}, 2: {2}, 3: {3}, 4: {4}, 5: {3, 4}, 6: {3}, 7: {1, 3}, 8: {1, 2, 3}, 9: {1, 2}}

graph = nx.from_edgelist(edge_labels, nx.DiGraph())

Graph(graph, node_layout='dot',
      node_labels=node_labels, node_label_fontdict=dict(size=21),
      edge_labels=edge_labels, edge_label_fontdict=dict(size=14), edge_label_rotate=False,
      node_color=color_map, node_edge_color=color_map, arrows=True
)

plt.show()
