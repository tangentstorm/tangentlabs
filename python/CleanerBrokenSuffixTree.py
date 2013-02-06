# object-oriented suffix tree implementation

class EndOfTheText:
    def __cmp__(self, other):
        return 1
    def __add__(self, n):
        return self
    def __sub__(self, n):
        return self
    def __str__(self):
        return "$"
   
START, END = -1, EndOfTheText()


class StateNode(object):
    def __init__(self, text, left, right):
        self.text = text
        self.left = left
        self.right = right

        self.kids = []
        self.seen = {}

        self.tokens = []
        self.data = {}
        
    def grow(self, token, index):
        if self.needToSplit(token):
            self.split(token, index)        
        for kid in self.kids:
            kid.grow(token, index)
        self.seen[token] = 1
        
    def split(self, token, edge):        
        newKid = Fragment(self.text, self.left + edge, END)
        self.kids.append(newKid)
        self.right = edge
        
    def needToSplit(self, token):
        res = 0
        #if not self.seen.has_key(token):
        #    res = 1
        #return res
        
    def show(self):
        head = str(self)
        tail = " ".join([x.show() for x in self.kids])
        return "(%s)" % " ".join((head, tail)).strip()

    def __str__(self):
        assert self.left != START
        if self.right is END:
            return self.text[self.left:] + "..."
        else:
            return self.text[self.left:self.right]

    ## statenode stuff ###

    def __getitem__(self, key):
        return self.data[key]
    def addTransition(self, token, left, right, state):
        if token not in self.tokens:
            self.tokens.append(token)
        self.data[token] = (Bounds(left, right), state)
    def contains(self, token):
        return self.data.has_key(token)
    def children(self):
        res = []
        for t in self.tokens:
            res.append(self.data[t])
        return tuple(res)


class Root(StateNode):
    def __init__(self, text):
        super(Root, self).__init__(text, START, END)        
    def __str__(self):
        return "^"
    def needToSplit(self, token):
        return not self.seen.has_key(token)

class Bottom(StateNode):
    def __init__(self, text, root):
        super(Bottom, self).__init__(text, START, END)
        for i in range(len(text)):
            self.addTransition(text[i], i, i, root)


class SuffixTree:
    def __init__(self, text):
        self.text = text
        
        self.tree = Root(text)        
        bottom = Bottom(text, self.tree)
        self.tree.sLink = bottom

        self.index = 0
        for token in text:
            self.index += 1
            self.tree.grow(token, self.index)

    def __str__(self):
        return self.tree.show()

if __name__=="__main__":
    def test(text, goal):
        actual = str(SuffixTree(text))
        assert actual == goal, actual

    test("", "(^)")
    test("m", "(^ (m...))")
    test("mi", "(^ (mi...) (i...))")
    test("mis", "(^ (mis...) (is...) (s...))")
    test("miss", "(^ (miss...) (iss...) (ss...))")
    test("missi", "(^ (missi...) (issi...) (s (s...) (i...)))")
    print "OK"
