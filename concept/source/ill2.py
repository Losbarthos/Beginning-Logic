import matplotlib.pyplot as plt
from igraph import Graph, plot

p = Graph(directed=True)

##
# Assumptions and Conclusion
#

p.add_vertices(5)
p.vs["label"] = ['c', 'a1', 'a2', '...', 'an']
p.vs["color"] = ['yellow', 'red', 'red', 'red', 'red']
p.vs["order"] = [1, 2, 3, 4, 5]
p.vs["size"] = [0.7,0.7,0.7,0.7,0.7]


##
# First Rule
#

p.add_vertices(3)
p.vs[5:8]["label"] = ['p1,1', ' ... ', 'p1,n1']
p.vs[5:8]["color"] = ['lightblue',  'lightblue', 'lightblue']
p.vs[5:8]["size"] = [0.7,0.7,0.7]
p.add_edge(p.vs.find(label='p1,1'), p.vs.find(label='c'))
p.add_edge(p.vs.find(label=' ... '), p.vs.find(label='c'))
p.add_edge(p.vs.find(label='p1,n1'), p.vs.find(label='c'))

p.es["label"] = ['ri1', 'ri1', 'ri1']

 
layout = p.layout("kk")
fig, ax = plt.subplots()
plot(p, layout=layout)
plot(p, layout=layout, target=ax, edge_label=p.es["label"])
plt.show()