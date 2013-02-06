# http://stackoverflow.com/questions/5094793/beginner-question-about-python
import random

def roll(size):
    return random.randint(1, size)

if True:
    class lifeform:
        def __init__(self, name):
            self.name = name
            self.attributes = { 'STR': 0, 'DEX': 0, 'CON': 0, 'INT': 0, 'WIZ': 0, 'CHA': 0, }

        def rollAttribute(self):

            # roll four 6sided di
            dice = [roll(6) for i in range(4)]

            # discard lowest roll
            return sum(dice) - min(dice)

        def rollStats(self):
            for key in self.attributes:
                self.attributes[key] = self.rollAttribute()

x = lifeform("test")
print x.attributes
x.rollStats()
print x.attributes

"""
    c:\michal>python roller.py
    {'DEX': 0, 'CHA': 0, 'INT': 0, 'STR': 0, 'WIZ': 0, 'CON': 0}
    {'DEX': 8, 'CHA': 11, 'INT': 12, 'WIS': 13, 'STR': 4, 'WIZ': 0, 'CON': 7}

    c:\michal>python roller.py
    {'DEX': 0, 'CHA': 0, 'INT': 0, 'STR': 0, 'WIZ': 0, 'CON': 0}
    {'DEX': 10, 'CHA': 13, 'INT': 13, 'WIS': 17, 'STR': 9, 'WIZ': 0, 'CON': 14}

    c:\michal>python roller.py
    {'DEX': 0, 'CHA': 0, 'INT': 0, 'STR': 0, 'WIZ': 0, 'CON': 0}
    {'DEX': 15, 'CHA': 9, 'INT': 17, 'WIS': 9, 'STR': 11, 'WIZ': 0, 'CON': 12}

    c:\michal>python roller.py
    {'DEX': 0, 'CHA': 0, 'INT': 0, 'STR': 0, 'WIZ': 0, 'CON': 0}
    {'DEX': 5, 'CHA': 15, 'INT': 12, 'WIS': 15, 'STR': 8, 'WIZ': 0, 'CON': 11}
"""
