# program to convert a stream of time codes to a table
from string import digits

class Reader(object):
    """
    Reads characters from a file or string iterator.
    Provides simple 1-character lookahead.
    """
    def __init__(self, char_gen):
        self.ch = None       # lookahead char
        self.gen = char_gen  # underlying char generator
        self.at_end = False  # end of file/stream/etc marker
        self.next_char()

    def next_char(self):
        """
        Populates self.ch and returns either the character
        or None for end of input.
        """
        if not self.at_end:
            try:
                self.ch = self.gen.next()
            except StopIteration:
                self.at_end = True
                self.ch = None
        return self.ch

class StreamParser(Reader):
    """
    This reads our data format  (T302 M20 M22 T303 M13 M35)
    and generates a stream of tuples.
    """
    def __iter__(self):
        while not self.at_end:
            yield self.next_tuple()

    # -- recursive descent parser ---

    def skip_whitespace(self):
        while self.ch and (ord(self.ch) <= ord(' ')):
            self.next_char()

    def next_int(self):
        res = []
        self.next_char()
        while self.ch and self.ch in digits:
            res.append(self.ch)
            self.next_char()
        return int(''.join(res))


    def next_tuple(self):
        self.skip_whitespace()
        if self.ch == 'T':
            return ('T', self.next_int(), '')
        elif self.ch == 'M':
            return ('M', '', self.next_int())
        else:
            raise "Error: Expected (T|M) but got:", self.ch

def tabulate(chars):
    """
    >>> tabulate(iter("T302 M20 M22 T303 M13 M35"))
    T  302     
    M        20
    M        22
    T  303     
    M        13
    M        35
    """
    for item in StreamParser(chars):
        print "{0}  {1:3}  {2:3}".format(*item)

if __name__=="__main__":
    # tabulate(iter("T302 M20 M22 T303 M13 M35"))
    import doctest
    doctest.testmod()
