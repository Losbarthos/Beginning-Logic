test1 = [['p', '(q ∧ ¬(q))', '¬(p)'], ['p', '(¬(p) ∧ ¬(¬(p)))', '¬(p)']]
test2 = ['p', '(q ∧ ¬(q))', '¬(p)', 'q']

def seperate(data, index=None):
	if index == None:
		head = data[0]
		origin = data[1:]
	else:
		head = data[index][0]
		origin = data[index][1:]

	return (head, origin)

print(seperate(test1,0))
print(seperate(test2))
print(seperate(test1,1))
