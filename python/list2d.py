"""
making a 2d container in python.
"""

def iterative_list2d(cols, rows):
   """
   Goal here is to make an M columns * N rows structure:
   
    [ [ (0,0), (1,0), ... (m-1,0)],
      [ (0,1), (1,1), ... (m-1,1)],
      .
      :
      [ (0,n-1), (1,n-1), ... (m-1,n-1)],
    ]

   This is a simple declarative approach.
   
   One downside of this structure is that the indices are
   "backwards": the grid is a list of rows, so when you say
   grid[ 0 ] you get a row, and grid[0][1] gives you 
   cell (1,0) in the picture above.
   """
   res = []
   for n in range(rows):
       row = []
       for m in range(cols):
           row.append(m,n)
       res.append(row)
   return res


def generative_list2d(cols, rows):
    """
    Same structure as iterative_list2d, but using 
    list comprehensions.

    [ [ (0,0), (1,0), ... (m-1,0)],
      [ (0,1), (1,1), ... (m-1,1)],
      .
      :
      [ (0,n-1), (1,n-1), ... (m-1,n-1)],
    ]
    """
    return [ [ (m,n) for m in range(rows) ] for n in range(cols) ]




## Here is a better way ( I think )
## By wrapping the structure in a class, we can
## clean it up considerably.

class List2D(object):
    """
    A class that uses 2d coordinates:
    
    >>> list2d = List2D(5, 3)
    >>> list2d.size
    (5, 3)
    >>> # fills with zeros by default
    >>> list2d[1, 2]
    0
    >>> list2d.fill(lambda x, y: (x, y))
    >>> list2d[1, 2]
    (1, 2)
    """
    def __init__(self, w, h, fill=lambda x,y: 0):
        """
        :: ( w: int, h: int, ( fill: x,y -> Any )? ) -> List2D
        """
        self.w = w
        self.h = h
        self.size = (w,h)
        self.data = [ [ fill(x,y) for x in range(w) ] for y in range(h) ]

    def __getitem__(self, xy):
        """
        :: [x,y] -> Any

        ex: myList2d[x,y]
        """
        x, y = xy
        return self.data[y][x]

    def __setitem__(self, xy, val):
        """
        :: [x,y] -> ()

        ex: myList2d[x,y] = 123
        """
        x, y = xy
        self.data[y][x] = val

    def fill(self, xyfunc):
        """
        :: (x,y -> Any) -> ()

        Updates the grid in place, using the result of xyfunc(x,y)
        as the value for each cell.
        """
        for y in range(self.h):
            for x in range(self.w):
                self[x,y] = xyfunc(x,y)

    def rows(self):
        """
        :: gen [[Any]]

        Iterates through the rows.

        >>> for row in List2D(2,2).rows():
        ...    print(row)
        [0, 0]
        [0, 0]
        """
        for row in self.data:
            yield row

    def values(self):
        """
        :: gen [Any]

        Iterates through the values without grouping.

        This is also the default __iter__ so,
        you don't need to write .vals() it explicitly:

        >>> for val in List2D(2,2):
        ...    print(val)
        0
        0
        0
        0
        """
        for row in self.data:
            for val in row:
                yield val

    def __iter__(self):
        """
        Same as .values()
        """
        return self.values()


    def keys(self):
        """
        :: gen [(x,y)]

        Iterate through the keys of the list2d, in
        "print" order (top to bottom, then left to right)

        >>> for x, y in List2D(2, 2).keys():
        ...     print x, y
        0 0
        1 0
        0 1
        1 1
        """
        for y in range(self.h):
            for x in range(self.w):
                yield x,y

    def items(self):
        """
        Loops through both the keys and the values.
        (By analogy with dict.items())

        >>> for xy, v in List2D(2, 2).items():
        ...     print xy, "->", v
        (0, 0) -> 0
        (1, 0) -> 0
        (0, 1) -> 0
        (1, 1) -> 0
        """
        return zip(self.keys(), self.values())

    def copy(self):
        """
        :: List2D
        
        Returns a copy of the data as new List2D of the same dimensions.
        """
        return List2D(self.w, self.h, lambda x,y : self[x,y])


if __name__=="__main__":
    import doctest
    doctest.testmod()
