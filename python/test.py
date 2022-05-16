from tkinter import *

def apply_text(lbl_control):
    lbl_control['state'] = 'normal' # change state back to normal
    lbl_control.insert(-1, "") # insert text
    lbl_control.insert(0, "This is some test!") # insert text
    lbl_control['state'] = 'readonly' # change state to readonly

master = Tk()

lbl = Entry(master, state="readonly")
btn = Button(master, text="apply", command=lambda: apply_text(lbl))


lbl.pack()
btn.pack()

mainloop()