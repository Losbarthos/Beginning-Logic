?- proof((([¬(q),p→q], []) ⊦ ¬(p)), P).
P = 
[[([¬q,p→q],[])⊦(¬p)], [[edge(¬ (¬p),¬p),edge(q∧ ¬q,¬p),rule(¬E,0)]],
[([¬q,p→q,¬ (¬p)],[])⊦(q∧ ¬q)],[[edge(q,q∧ ¬q),edge(¬q,q∧ ¬q),rule(∧I,1)]],
[([¬q,p→q,¬ (¬p)],[])⊦q],[[edge(p,q),edge(p→q,q),rule(→E,2)]],
[([¬q,¬ (¬p)],[])⊦p],[[edge(¬p,p),edge(¬p∧ ¬ (¬p),p),rule(¬E,3)]],
[([¬q,¬ (¬p),¬p],[])⊦(¬p∧ ¬ (¬p))],[[edge(¬p,¬p∧ ¬ (¬p)),edge(¬ (¬p),¬p∧ ¬ (¬p)),rule(∧I,4)]]] ;





P = [[([¬q,p→q],[])⊦(¬p)],[[edge(¬ (¬p),¬p),edge(q∧ ¬q,¬p),rule(¬E,0)]],[([¬q,p→q,¬ (¬p)],[])⊦(q∧ ¬q)],[[edge(p,q),edge(p→q,q),rule(→E,1)]],[([¬q,p→q,¬ (¬p)],[q])⊦(q∧ ¬q)],[[edge(q,q∧ ¬q),edge(¬q,q∧ ¬q),rule(∧I,2)]],[([¬q,¬ (¬p)],[])⊦p],[[edge(¬p,p),edge(¬p∧ ¬ (¬p),p),rule(¬E,3)]],[([¬q,¬ (¬p),¬p],[])⊦(¬p∧ ¬ (¬p))],[[edge(¬p,¬p∧ ¬ (¬p)),edge(¬ (¬p),¬p∧ ¬ (¬p)),rule(∧I,4)]]] ;
P = [[([¬q,p→q],[])⊦(¬p)],[[edge(p,¬p),edge(q∧ ¬q,¬p),rule(¬I,0)]],[([¬q,p→q,p],[])⊦(q∧ ¬q)],[[edge(q,q∧ ¬q),edge(¬q,q∧ ¬q),rule(∧I,1)]],[([¬q,p→q,p],[])⊦q],[[edge(p,q),edge(p→q,q),rule(→E,2)]]] ;
P = [[([¬q,p→q],[])⊦(¬p)],[[edge(p,¬p),edge(q∧ ¬q,¬p),rule(¬I,0)]],[([¬q,p→q,p],[])⊦(q∧ ¬q)],[[edge(p,q),edge(p→q,q),rule(→E,1)]],[([¬q,p→q,p],[q])⊦(q∧ ¬q)],[[edge(q,q∧ ¬q),edge(¬q,q∧ ¬q),rule(∧I,2)]]] ;
