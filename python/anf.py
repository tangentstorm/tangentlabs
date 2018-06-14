"""
a zdd-like data structure for working with algebraic normal form.
"""
import unittest
from functools import reduce

def anf(terms):
    return ANF.from_terms(terms)

class ANF(object):

    @staticmethod
    def empty():
        return ANF.from_term('0')

    @staticmethod
    def hitch(var, anf):
        return ANF(var=var, inc=False, lo=None, hi=anf)

    @staticmethod
    def from_term(term):
        if term in '01': result=ANF(var=term, inc=term=='1', lo=None, hi=None)
        else:
            xs = reversed(sorted(term))
            result = ANF(var=next(xs), inc=True, lo=None, hi=None)
            for x in xs: result = ANF.hitch(x, result)
        return result

    @staticmethod
    def from_terms(terms):
        terms = terms.split() if type(terms)==str else terms[:]
        if terms: return reduce(XOR, [ANF.from_term(t) for t in terms])
        else: return ANF.empty()

    def __init__(self, var, inc, lo, hi):
        self.var = '' if var in '01' else var
        self.inc = inc
        self.lo = lo
        self.hi = hi

    def __str__(self):
        v = self.var or '%i' % self.inc
        if self.var == '' and (self.lo == self.hi == None): return '(%s)' % v
        return ' '.join(['(%s%s' % ('*' if self.inc else '', v),
                         str(self.lo) if self.lo else '-',
                         str(self.hi) if self.hi else '-']) + ')'

    def gen_terms(self):
        """generates a series of terms"""
        if self.inc: yield self.var or '1'
        if self.hi:
            for x in self.hi.gen_terms(): yield self.var + x
        if self.lo:
            for x in self.lo.gen_terms(): yield x

    def terms(self):
        return ' '.join(self.gen_terms())

    def is_leaf(self):
        return self.lo is None and self.hi is None


def XOR(x0,y0):
    if x0 is None: return y0
    if y0 is None: return x0
    x,y = (x0,y0) if x0.var <= y0.var else (y0,x0)
    if x.var == '' and not x.inc: return y0
    if x.var == y.var:
        r = ANF(x.var, inc=(x.inc ^ y.inc), lo=XOR(x.lo, y.lo), hi=XOR(x.hi,y.hi))
        if (not r.inc) and (r.lo == r.hi == None): return ANF.empty()
        else: return r
    else: return ANF(x.var, inc=x.inc, lo=XOR(x.lo, y), hi=x.hi)

def AND(x0,y0):
    x,y = (x0,y0) if x0.var <= y0.var else (y0,x0)
    if x.is_leaf():
        if y.is_leaf():
            assert y.inc, "leaves should always be incuded in the set."
            if x.var==y.var: return x
            else: return ANF(var=x.var, inc=False, lo=None, hi=y)
        else: # y is not a leaf
            return XOR(ANF(var=y.var, inc=y.inc, lo=None, hi=y.hi),
                       ANF(var=y.var, inc=False, lo=None, hi=y.lo))
    else: # neither is a leaf:
        raise NotImplementedError



class ANFTest(unittest.TestCase):

    def cheq(self, terms, string):
        """check for equality"""
        self.assertEqual(str(ANF.from_terms(terms)), string)

    def test_from_term(self):
        chk = lambda t,s : self.assertEqual(str(ANF.from_term(t)), s)
        chk('',    "(0)")
        chk('0',   "(0)")
        chk('1',   "(1)")
        chk('a',   "(*a - -)")
        chk('ab',  "(a - (*b - -))")
        chk('ac',  "(a - (*c - -))")
        chk('abc', "(a - (b - (*c - -)))")

    def test_from_terms(self):
        chk = lambda t,s : self.assertEqual(str(ANF.from_terms(t)), s)
        chk('',        "(0)")     # this is the empty set.
        chk('0',       "(0)")     # same
        chk('1',       "(1)")     # term should be same as above
        chk('a',      "(*a - -)") # xor/a     = a
        chk('a a',     "(0)")     # xor/a,a   = empty
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

if __name__=="__main__":
    unittest.main()
