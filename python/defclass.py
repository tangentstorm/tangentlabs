"""
I accidentally typed 'def' somewhere instead of 'class'
and was surprised to get an error about metaclasses.
it seems you may be able to subclass functions if you
get the metaclass right.

No idea what this would mean or why it might be useful yet.
"""

def F():
    print('I am a function!')

class C(F):
    def __init__(self):
        print(hello)


if __name__=="__main__":
    c = c()
    c()

output_py27="""\
Traceback (most recent call last):
  File "defclass.py", line 13, in <module>
    class C(F):
TypeError: Error when calling the metaclass bases
    function() argument 1 must be code, not str
"""

output_py34="""\
Traceback (most recent call last):
  File "defclass.py", line 13, in <module>
    class C(F):
TypeError: function() argument 1 must be code, not str
"""
