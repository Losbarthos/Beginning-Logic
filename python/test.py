from tkinter import *
from tkinter import ttk
import matplotlib
import matplotlib.pyplot as plt
matplotlib.use('GTK3Agg')

print(matplotlib.__version__)
def helloCallBack():
    plt.plot([1,2,3],[5,7,4])
    plt.show()

root = Tk()
B = Button(root, text ="Hello", command = helloCallBack)
B.pack()

root.mainloop()