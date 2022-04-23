
import pandas as pd
import numpy as np

if __name__ == '__main__':
    data1 = {'row_1': [3, 2, 1, 0], 'row_2': ['a', 'b', 'c', 'd']}
    
    df1 = pd.DataFrame.from_dict(data1, orient='index', columns=['A', 'B', 'C', 'D'])
    data2 = {'col_1': [3, 2, 1, 0], 'col_2': ['a', 'b', 'c', 'd']}

    df2 = pd.DataFrame.from_dict(data2)
    df3 = pd.DataFrame(np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9]]),
                   columns=['a', 'b', 'c'])
    data = np.array([(1, 2, 3), (4, 5, 6), (7, 8, 9)],

                dtype=[("a", "i4"), ("b", "i4"), ("c", "i4")])

    df4 = pd.DataFrame(data, columns=['c', 'a'])

    l_input = [df1, df2, df1, df3, df4, df4, df1, df3]
    l_aim = [df1, df2, df3, df4]
    if df1.equals(df1):
        print("yes")