"""
This module replaces its entry in sys.modules
with a factory class so you can create "quoted"
names on the fly:

>>> from symbols import a,b,c
>>> a
Symbol('a')
>>> print(a)
$a

Motivation for this technique:

http://web.archive.org/web/20081228090759/http://withoutane.com/rants/2008/12/arlo-generic-combinators-for-python
"""
import sys

class Symbol(object):
    """
    an object that represents a symbol
    """
    def __init__(self, sym):
        self.iden = sym
        
    def __str__(self):
        return '$%s' % self.iden

    def __repr__(self):
        return "Symbol('%s')" % self.iden

class SymbolModule(object):
    """
    This is a simple factory class
    masquerading as a module.
    """
    Symbol = Symbol
    def __getattr__(self, attr):
        return self.Symbol(attr)

sys.modules['symbols'] = SymbolModule()
