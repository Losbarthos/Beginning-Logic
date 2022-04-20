import matplotlib.pyplot as plt
import networkx as nx

def view_graph(graph, node_labels, edge_labels):
    '''
        Plots the graph
    '''
    pos = nx.spring_layout(graph)
    nx.draw(graph, pos, node_color=color_map)
    nx.draw_networkx_labels(graph, pos, labels=node_labels)
    nx.draw_networkx_edge_labels(graph, pos, edge_labels=edge_labels)
    plt.axis('off')
    plt.show()

index_to_name = {1: "Paul", 2: "Magda", 3: "Paul", 4: "Anna", 5: "Marie", 6: "John", 7: "Mark"}
color_map2 = {1: "blue", 2: "green", 3: "blue", 4: "lightgreen", 5: "lightgreen", 6: "lightblue", 7: "lightblue"}
color_map = ["blue", "green", "blue", "lightgreen", "lightgreen", "lightblue", "lightblue"]

relation = {}
relation[(1, 4)] = "dad"
relation[(2, 4)] = "mom"
relation[(1, 5)] = "dad"
relation[(2, 5)] = "mom"
relation[(3, 6)] = "dad"
relation[(4, 6)] = "mom"
relation[(3, 7)] = "dad"
relation[(4, 7)] = "mom"

g = nx.from_edgelist(relation, nx.DiGraph())

view_graph(g, index_to_name, relation)
