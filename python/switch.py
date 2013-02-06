## case statement ################################
##
## this idea is taken from:
## http://aspn.activestate.com/ASPN/Cookbook/Python/Recipe/410692
##
## it's modified slightly because I didn't want
## the "fall through" behavior that required break

class switch(object):
    """
    syntactic sugar for multiple dispatch
    """
    def __init__(self, value):
        self.value = value

    def __iter__(self):
        """
        this lets you do 'for case in switch()'
        """
        yield self.match
        raise StopIteration
    
    def match(self, *args):
        return self.value in args

