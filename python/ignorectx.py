from __future__ import with_statement
from contextlib import contextmanager

"""
[2008.1008 09:05PM] was just messing around here.
I thought maybe I could trick the context manager
into letting me run arbitrary code, I don't think
I can do that from python. Maybe if I defined my
context manager in an exenstion library where I
had access to the virtual machine, though...
"""

@contextmanager
def ignored():
    print "["
    try:
        yield
    except NameError:
        pass
    finally:
        print "]"

with ignored() as macro:
    +macro(
    print 'hello!'
    -macro
    
print macro

