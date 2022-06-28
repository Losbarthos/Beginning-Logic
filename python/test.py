
import pandas as pd
import numpy as np

def generate_tables():
    with open('tables.tex', 'w') as f:
        # header

        f.write("% !TeX TS-program = lualatex\n") 
        f.write("\\documentclass{article}\n")
        f.write("\\usepackage{booktabs}\n")
        f.write("\\usepackage{unicode-math}\n")
        f.write("\\begin{document}\n")

        fooder = "\\end{document}\n"

        for i in range(10):
            df = pd.DataFrame(np.random.random((5, 5)))
            latex_table = df.to_latex(index=False,header=False,escape=False)
            f.write(f"Table {i}:")
            f.write("\n\\\\\n")
            f.write(latex_table)
            f.write("\\\\[2\\baselineskip]\n")

        f.write(fooder)

generate_tables()

print(f"{{}}")