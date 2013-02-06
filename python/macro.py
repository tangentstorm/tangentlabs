import sys
# effbot answers my newbie python question from 2000: 
# http://groups.google.com/group/comp.lang.python/msg/9e826841322173de?hl=en

"""
Here's what I want:

    @macro
    def inc(x):
        x += 1

    y = 2
    inc(y)
    assert y == 3

This is possible, using effbot's trick.

1. macro() actually parses the file it's in
   (so you probably couldn't define it at the prompt)

2. the function it returns figures out where it is,
   parses that line using ast.py (so again, not from
   the prompt), rewrites the code on the fly, and then
   uses effbot's magic trick.
"""

def magic_eval(thunk):
    try:
        raise None
    except:
        frame = sys.exc_traceback.tb_frame.f_back
        return eval(thunk, frame.f_globals, frame.f_locals)

def macro(f):
    def f2(*a, **kw):
        magic_eval(lambda : f(*a, **kw))
    return f2

@macro
def inc(x):
    x += 1

x = 5
inc(x)
print "x is", x
    
