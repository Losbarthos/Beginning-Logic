import matplotlib.pyplot as plt
import networkx as nx

from netgraph._main import EmphasizeOnHoverGraph

if __name__ == '__main__':

    node_labels = {1: 'p→q', 2: '¬q', 3: '¬ (¬p)', 4: '¬p', 5: '¬p∧ ¬ (¬p)', 6: 'p', 7: 'q', 8: 'q∧ ¬q', 9: '¬p'}
    color_map = {1: 'red', 2: 'red', 3: 'red', 4: 'red', 5: 'lightblue', 6: 'lightblue', 7: 'lightblue', 8: 'lightblue', 9: 'blue'}
    edge_labels = {(3, 5): '∧I', (4, 5): '∧I', (4, 6): '¬E', (5, 6): '¬E', (1, 7): '→E', (6, 7): '→E', (2, 8): '∧I', (7, 8): '∧I', (8, 9): '¬E', (3, 9): '¬E'}
    highlight = {1: [1], 2: [2], 3: [3], 4: [4], 5: [3, 4, 5], 6: [3, 6], 7: [1, 3, 7], 8: [1, 2, 3, 8], 9: [1, 2, 9]}


    graph = nx.from_edgelist(edge_labels, nx.DiGraph()) 

    fig, ax = plt.subplots(figsize=(10, 10))
    g = EmphasizeOnHoverGraph(graph, node_layout='dot', 
        node_color=color_map, mouseover_highlight_mapping=highlight, edge_label_fontdict=dict(size=14), 
        node_label_fontdict=dict(size=21), node_labels=node_labels, edge_labels=edge_labels, ax=ax)
    plt.show()