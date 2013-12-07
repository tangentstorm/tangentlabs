http://groups.google.com/groups?hl=en&th=30ccd76f95f43db9&rnum=2

import sys
def IIF(exp, t, f):
    try:
        raise "foo!"
    except:
        tb = sys.exc_traceback

    fr = tb.tb_frame.f_back
    locs = fr.f_locals
    globs = fr.f_globals

    expVal = eval(exp, locs, globs)
    if expVal:
        return eval(t, locs, globs)
    else:
        return eval(f, locs, globs)


import sys

def magic_eval(s):
    try:
        raise None
    except:
        frame = sys.exc_traceback.tb_frame.f_back
        return eval(s, frame.f_globals, frame.f_locals)


def _upExec(python, g, l):
    """
    python black magic.
    returns the namespace of the caller's caller :)
    see http://groups.google.com/groups?hl=en&th=30ccd76f95f43db9&rnum=2
    """
    try:
        raise None
    except:
        upUpFrame = sys.exc_traceback.tb_frame.f_back.f_back
        assert g is upUpFrame.f_globals
        assert l is upUpFrame.f_locals
        exec python in upUpFrame.f_globals, upUpFrame.f_locals

def define(name, value, g, l):
    _upExec("global %s; %s = %s" % (name, name, value), g, l)

if __name__=="__main__":
    define("a",100)
    print a

