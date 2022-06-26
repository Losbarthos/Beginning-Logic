import pandas as pd
import numpy as np

df1 = pd.DataFrame(np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9]]),
                   columns=['a', 'b', 'c'])
df2 = pd.DataFrame(np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9], [11, 12, 13]]),
                   columns=['a', 'b', 'c'])
df3 = pd.DataFrame(np.array([[1, 2, 3], ['x', 'y', 'z']]),
                   columns=['a', 'b', 'c'])

idx = [1,2,3]


lst = []

lst.append(df1)
lst.append(df2)
lst.append(df3)


lst_srt = sorted(lst, key=len)

i = 0
idx_lst = []
for a in lst_srt:
    i = 0   
    for b in lst:
        i = i + 1
        if a.equals(b):
            idx_lst.append(i)
            break

print(idx_lst)

print(lst_srt)