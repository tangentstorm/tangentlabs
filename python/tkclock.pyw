from Tkinter import *
import time

# this is an arbitrary value that we add to the date
# so that the hour starts at 0. (Otherwise, the time
# starts around 7pm on 12/31/1969
OFFSET = time.mktime((2000, 1, 1, 0, 0, 0, 0, 0, 0))


def currentTime(start):
    return "%02i:%02i:%02i"  % time.localtime(OFFSET + time.time() - start)[3:6]

class Clock(Frame):
    def showTime(self, *args):
        self.text.configure(text = currentTime(self.start))
        self.after(10, self.showTime)

    def __init__(self, master=None):
        Frame.__init__(self, master)
        Pack.config(self) #??
        self.start = time.time()
        self.text = Label(self, {"text": currentTime(self.start),
                                 "font": (('Verdana'), 40)})
        self.text.pack()
        self.after(10, self.showTime)


clock  = Clock()
clock.mainloop()

