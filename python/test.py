import tkinter as tk
class Application(tk.Frame):
    def __init__(self, master):
        tk.Frame.__init__(self, master)
        self.text = tk.Text(master)        
        self.text.pack()
    def show_dict(self, d):
        for k, v in d.items():
            self.text.insert(tk.END, "key = {}, val = {}\n".format(k, v))
     
root = tk.Tk()
app = Application(root)
app.show_dict({'Username': 0, 'Username2': 2})
app.mainloop()