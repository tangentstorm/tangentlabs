"""
a zdd-like data structure for working with the algebraic normal form (xor of ands) of boolean functions.
ANF has various nice properties (xor(f,g) is trivial, not(f) is just xor(f,1), ...)
Unfortunately, the AND operation is very expensive, as it amounts to the multiplication of polynomials.
"""
import unittest
from functools import reduce

def anf(terms):
    return ANF.from_terms(terms)

class ANF(object):

    @staticmethod
    def false():
        return ANF(var='', inc=0, lo=None, hi=None)

    @staticmethod
    def hitch(var, anf):
        return ANF(var=var, inc=0, lo=None, hi=anf)

    @staticmethod
    def from_term(term):
        if term == '':    result=ANF(var='', inc=0, lo=None, hi=None)
        elif term == '1': result=ANF(var='', inc=1, lo=None, hi=None)
        else:
            xs = reversed(sorted(set(term)))
            result = ANF(var=next(xs), inc=1, lo=None, hi=None)
            for x in xs: result = ANF.hitch(x, result)
        return result

    @staticmethod
    def from_terms(terms):
        terms = terms.split() if type(terms)==str else terms[:]
        if terms: return reduce(XOR, [ANF.from_term(t) for t in terms])
        else: return ANF.false()

    def __init__(self, var, inc, lo, hi):
        self.var = var
        self.inc = inc
        self.lo = lo
        self.hi = hi

    def __str__(self):
        if self.is_false(): return '( )'
        v = self.var or '1'
        if self.var == '' and (self.lo == self.hi == None): return '(%s)' % v
        return ' '.join(['(%s%s' % ('*' if self.inc else '', v),
                         str(self.lo) if self.lo else '-',
                         str(self.hi) if self.hi else '-']) + ')'
    def __repr__(self):
        return str(self)

    def gen_terms(self):
        """generates a series of terms"""
        if self.is_false(): return
        if self.inc: yield self.var or '1'
        if self.hi:
            for x in self.hi.gen_terms(): yield self.var + x
        if self.lo:
            for x in self.lo.gen_terms(): yield x

    def terms(self):
        return ' '.join(self.gen_terms())

    def is_leaf(self):
        return self.lo is None and self.hi is None

    def is_false(self):
        return self.var is '' and not self.inc

    def is_true(self):
        return self.var is '' and self.is_leaf()


def XOR(x0,y0):
    if x0 is None: return y0
    if y0 is None: return x0
    x,y = (x0,y0) if x0.var <= y0.var else (y0,x0)
    if x.is_false(): return y0
    if x.var == y.var:
        r = ANF(x.var, inc=(x.inc ^ y.inc), lo=XOR(x.lo, y.lo), hi=XOR(x.hi,y.hi))
        if (not r.inc) and (r.lo == r.hi == None): return ANF.false()
        else: return r
    else: return ANF(x.var, inc=x.inc, lo=XOR(x.lo, y), hi=x.hi)


def NAIVE_AND(x,y):
    """full cartesian product. (slow)"""
    res = ANF.false()
    for xt0 in x.gen_terms():
        for yt0 in y.gen_terms():
            (xt,yt) = (xt0, yt0) if xt0<=yt0 else (yt0,xt0)
            res = XOR(res, anf(yt if xt == '1' else xt+yt))
    return res


def AND(x0,y0):
    x,y = (x0,y0) if x0.var <= y0.var else (y0,x0)
    if x.is_false(): return x
    if x.is_true(): return y
    if x.is_leaf():
        if y.is_leaf():
            assert y.inc, "leaves should always be incuded in the set. (got: %s)" % y
            if x.var==y.var: return x
            else: return ANF(var=x.var, inc=0, lo=None, hi=y)
        else: # x is a leaf, y is not
            if x.var==y.var: return ANF(var=x.var, inc=y.inc, lo=None, hi=XOR(y.lo, y.hi))
            else: return ANF(var=x.var, inc=0, lo=None, hi=y) # otherwise, just prepend x (which is no longer in the set)
    else: # x is not a leaf, so we have to append y to the end of x
        return NAIVE_AND(x0,y0)
        print("x:", x)
        print("y:", y)
        raise NotImplementedError("complex case")



class ANFTest(unittest.TestCase):

    def cheq(self, terms, string):
        """check for equality"""
        self.assertEqual(str(ANF.from_terms(terms)), string)

    def test_from_term(self):
        chk = lambda t,s : self.assertEqual(str(ANF.from_term(t)), s)
        chk('',    "( )")
        chk('1',   "(1)")
        chk('a',   "(*a - -)")
        chk('aa',  "(*a - -)")
        chk('ab',  "(a - (*b - -))")
        chk('ac',  "(a - (*c - -))")
        chk('abc', "(a - (b - (*c - -)))")

    def test_from_terms(self):
        chk = lambda t,s : self.assertEqual(str(ANF.from_terms(t)), s)
        chk('',        "( )")     # this is false
        chk('1',       "(1)")     # this is true
        chk('a',      "(*a - -)") # xor/a     = a
        chk('a a',     "( )")     # xor/a,a   = false
        chk('a a a',  "(*a - -)") # xor/a,a,a = a
        chk('1 a', "(*1 (*a - -) -)")
        chk('a b', "(*a (*b - -) -)")
        chk('b a', "(*a (*b - -) -)")

    def test_terms(self):
        chk = lambda t,s : self.assertEqual(anf(t).terms(), s)
        chk('a', 'a')
        chk('1', '1')
        chk('a b', 'a b')
        chk('a ab','a ab')
        chk('1 a', '1 a')
        chk('1 a b ab', '1 a ab b')

    def test_xor(self):
        def chk(x,y,z):
            a,b = anf(x), anf(y); r = XOR(a,b); t = r.terms()
            self.assertEqual(t, z, 'expect: %s; got: %s; anf: %r XOR %r ==> %r' % (z,t,a,b,r))
        chk('a', 'a', '')
        chk('a', '1', '1 a')

    def chk_and(self, x,y,z):
        a,b = anf(x), anf(y); r = AND(a,b); t = r.terms()
        self.assertEqual(t, z, 'expect: %s; got: %s; anf: %r AND %r ==> %r' % (z,t,a,b,r))

    def test_and_simple_x(self):
        """check 'and' when x is a leaf"""
        chk = self.chk_and
        chk('', '', '')
        chk('', '1', '')
        chk('', 'a', '')
        chk('1', '', '')
        chk('1', '1', '1')
        chk('1', 'a', 'a')
        chk('a', 'a', 'a')
        chk('a', 'ab', 'ab')
        chk('a', 'bc', 'abc')
        chk('1', '1 a', '1 a')
        chk('1', 'a b', 'a b')
        chk('a', 'a b', 'a ab')

    def test_and_nonleaf_x(self):
        """check 'and' when x is not a leaf"""
        chk = self.chk_and
        chk('1 a', 'a', '')
        chk('a b', 'b', 'ab b')
        chk('a b', 'ab', '')
        chk('a b', 'bc', 'abc bc')
        chk('a b', 'b c', 'ab ac b bc')
        chk('a c', 'b d', 'ab ad bc cd')
        chk('a ab c', 'b d', 'abd ad bc cd')
        chk('a ab c', '1 b d', 'a ab abd ad bc c cd') # ~:/a,ab,ad,ab,ab,abd,c,bc,cd

    def test_and_complicated(self):
        chk = self.chk_and
        chk('ab cd', 'ad bc', 'abc abd acd bcd')
        chk('ae bc d', 'ab c de', 'abc abd abe ace ade bc bcde cd de')
        chk('a cd gk i jn', 'b ef hl im j',
            'ab aef ahl aim aj bcd bgk bi bjn cdef cdhl cdim cdj efgk efi efjn ghkl gikm gjk hil hjln ij ijmn im jn')

if __name__=="__main__":
    unittest.main()
