import matplotlib.pyplot as plt
from igraph import Graph, plot

p = Graph(directed=True)

##
# Assumptions and Conclusion
#

p.add_vertices(5)
p.vs["label"] = ['Conclusion', 'Assumption 1', 'Assumption 2', '...', 'Assumption n']
p.vs["color"] = ['yellow',  'red',          'red',          'red', 'red'         ]
p.vs["order"] = [1, 2, 3, 4, 5]


##
# First Rule
#

p.add_vertices(3)
p.vs[5:8]["label"] = ['Condition 1', ' ... ', 'Condition n1']
p.vs[5:8]["color"] = ['lightblue',  'lightblue', 'lightblue']
p.add_edge(p.vs.find(label='Condition 1'), p.vs.find(label='Conclusion'))
p.add_edge(p.vs.find(label=' ... '), p.vs.find(label='Conclusion'))
p.add_edge(p.vs.find(label='Condition n1'), p.vs.find(label='Conclusion'))

p.es["label"] = ['Rule i', 'Rule i', 'Rule i']

 
layout = p.layout("kk")
fig, ax = plt.subplots()
plot(p, layout=layout)
plot(p, layout=layout, target=ax, edge_label=p.es["label"])
plt.show()