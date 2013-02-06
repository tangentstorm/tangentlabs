import sys
from Tkinter import *

def main():
    root = Tk()
    button = Button(root)
    button['text'] = 'Hello'
    button['command'] = quit_callback
    button.pack()
    c = Canvas(root)
    c.pack()

    # draw a piano:
    # background:
    c.create_rectangle(0, 0, 310, 45, fill="navy")

    # white keys:
    for note in range (1, 30):
        c.create_rectangle(note * 10, 20, note*10 + 10, 50, fill="white")

    # two loops, because it draws on top of each other:
    # assume 1 = the note "c"
    for note in range (1, 28):
        if (note % 7) in (1, 2, 4, 5, 6):
            c.create_rectangle(note * 10 + 7, 20, note * 10 + 12, 40, \
                               fill="black")
    root.mainloop()

def quit_callback():
    sys.exit(0)

main()
