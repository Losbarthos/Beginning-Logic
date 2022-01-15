import matplotlib.pyplot as plt
from igraph import Graph, plot

p = Graph(directed=True)

p.add_vertices(5)
p.vs["label"] = ['c', 'a1', 'a2', '...', 'an']
p.vs["color"] = ['lightblue', 'red', 'red', 'red', 'red']
p.vs["order"] = [1, 2, 3, 4, 5]
p.vs["size"] = [0.7,0.7,0.7,0.7,0.7]

print(p)
 
layout = p.layout("kk")
fig, ax = plt.subplots()
plot(p, layout=layout)
plot(p, layout=layout, target=ax)
plt.show()