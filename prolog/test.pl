:-op(800, fx, ¬).
:-op(801, xfy, ∧).
:-op(802, xfy, ∨).
:-op(803, xfy, →).
:-op(804, xfy, ↔).


d = proof{1: ¬q, 2:p→q, 3: ¬ (¬p), 4: ¬p, 5:[edge(¬p, ¬p∧ ¬ (¬p)), edge(¬ (¬p), ¬p∧ ¬ (¬p)), rule('∧I')], 6:[edge(¬p, p), edge(¬p∧ ¬ (¬p), p), rule('¬E')], 7:[edge(p, q), edge(p→q, q), rule('→E')], 8:[edge(q, q∧ ¬q), edge(¬q, q∧ ¬q), rule('∧I')], 9:[edge(¬ (¬p), ¬p), edge(q∧ ¬q, ¬p), rule('¬E')]}. 

