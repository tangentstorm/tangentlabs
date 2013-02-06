# http://stackoverflow.com/questions/6557407/triple-inheritance-causes-metaclass-conflict-sometimes


class MetaA(type):
    pass

class MetaB(type):
    pass

class A:
    __metaclass__ = MetaA
class B:
    __metaclass__ = MetaB


"""
    >>> class Broken(A, B): pass
    ... 
    Traceback (most recent call last):
      File "<stdin>", line 1, in <module>
    TypeError: Error when calling the metaclass bases
      metaclass conflict: the metaclass of a derived class must be a (non-strict)
      subclass of the metaclasses of all its bases
"""

class MetaAB(MetaA, MetaB):
    pass

class Fixed(A, B):
    __metaclass__ = MetaAB


