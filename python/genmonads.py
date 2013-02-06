
# generator monads
# (an experiment)

def compose(f,g):
    return lambda *args : f(*g(*args))

#########
# first, some monad examples, from:
# http://sigfpe.blog1pot.com/2006/08/you-could-have-invented-monads-and.html
def f(aFloat) : return aFloat+1
def g(aFloat) : return aFloat+2
def f1(aFloat) : return [f(aFloat) , "f was called."]
def g1(aFloat) : return [g(aFloat) , "g was called."]

def ugly(x):
    y,s = g1(x)
    z,t = f1(y)
    return (z, s+t)

assert ugly(0) == (3, "g was called.f was called."), ugly(0)

def bind(f0):
    def _(gx, gs):
        (fx, fs) = f0(gx)
        return (fx, gs+fs)
    return _

    
assert compose(bind(f1), g1)(0) == (3, "g was called.f was called.")

def unit(x): return (x, "")
def lift(f,x): return (f, x, "")


#########
# so can we do the same thing with generators?

def f(aFloat) : yield aFloat+1
def g(aFloat) : yield aFloat+2

def unit(x): yield x

def lift(f): yield f()
