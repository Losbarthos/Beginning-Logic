import os

def read_rules(file_path):
    with open(file_path, 'r') as f:
        lines = f.readlines()
    rules = [(line.split("⊢")[0].split(","), line.split("⊢")[1].strip()) for line in lines]
    return rules

def rule(l_in, i):
    current_file = os.path.abspath(__file__)
    parent_directory = os.path.dirname(os.path.dirname(current_file))
    axioms_file_path = os.path.join(parent_directory, "data", "axioms.txt")
    rules = read_rules(axioms_file_path)

    left, right = rules[i - 1]

    if all(axiom.strip() in l_in for axiom in left) and right not in l_in:
        return [right] + l_in
    else:
        return False

if __name__ == '__main__':
    l_in = ['a∧b']
    l_out = rule(l_in, 3)
    print(l_out)