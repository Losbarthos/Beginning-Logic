import matplotlib.pyplot as plt
from igraph import Graph, plot

p = Graph(directed=True)

p.add_vertices(5)
p.vs["label"] = ['Conclusion', 'Assumption 1', 'Assumption 2', '...', 'Assumption n']
p.vs["color"] = ['lightblue',  'red',          'red',          'red', 'red'         ]
p.vs["order"] = [1, 2, 3, 4, 5]

print(p)
 
layout = p.layout("kk")
fig, ax = plt.subplots()
plot(p, layout=layout)
plot(p, layout=layout, target=ax)
plt.show()