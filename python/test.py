import tkinter as tk
import tkinter.ttk as ttk
import threading


class ProgressbarApp(threading.Thread):

    def __init__(self, max_value: int):
        self.max_value = max_value

        self.root = None
        self.pb = None

        threading.Thread.__init__(self)
        self.lock = threading.Lock()    # (1)
        self.lock.acquire()             # (2)
        self.start()

        # (1) Makes sure progressbar is fully loaded before executing anything
        with self.lock:
            return

    def close(self):
        self.root.quit()

    def run(self):

        self.root = tk.Tk()
        self.root.protocoll("WM_DELETE_WINDOW", disable_event)

        self.pb = ttk.Progressbar(self.root, orient='horizontal', length=400, mode='determinate')
        self.pb['value'] = 0
        self.pb['maximum'] = self.max_value
        self.pb.pack()

        self.lock.release()             # (2) Will release lock when finished
        self.root.mainloop()

    def update(self, value: int):
        self.pb['value'] = value

if __name__ == '__main__':
    interval = 100000
    my_pb = ProgressbarApp(interval)

    for i in range(interval):
        my_pb.update(i)

    my_pb.close()

    # Other stuff goes on . . .
