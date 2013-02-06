# SuffixTree for python
#
# loosely based on javascript from:
# http:#www.csse.monash.edu.au/~lloyd/tildeAlgDS/Tree/Suffix/
# which in turn was based on:
# from E.Ukkonen, On-Line Construction of Suffix Trees ***
#                 Algorithmica 14(3) pp 249-260, 1995  ***
# (U. Helsinki, Finland)


import sys
true, false = 1, 0

class FarRight:
    def __cmp__(self, other):
        return 1
    def __add__(self, n):
        return self
    def __sub__(self, n):
        return self
    def __str__(self):
        return "$"
FarRight = FarRight()


class Bounds:
    def __init__(self, left, right):
        self.left = left
        self.right = right
    def isEmpty(self):
        return self.width() == 0
    def width(self):
        return self.right - self.left
    def __repr__(self):
        return "%s:%s" % (self.left, self.right)
        

class StateNode:
    """
    We are nodes in the suffix tree.
    
    Our "transitions" are the next nodes, or in other words,
    our OWN suffixes.

    For example, in the string, "abacd", the transitions for
    the state "a" are "bacd" and "cd".
    """
    def __init__(self, text):
        self.tokens = []
        self.kids = {}
        self.text = text
    def __getitem__(self, key):
        return self.kids[key]
    def addTransition(self, token, left, right, state):
        if token not in self.tokens:
            self.tokens.append(token)
        self.kids[token] = (Bounds(left, right), state)
        state.bounds = Bounds(left, right)
    def contains(self, token):
        return self.kids.has_key(token)
    def children(self):
        res = []
        for t in self.tokens:
            res.append(self.kids[t])
        return tuple(res)

class SuffixTree:
    def __init__(self, text):
        self.text = text
        self.root = StateNode(text)
        self.createInitialTransitions()
        self.buildTree()

    def createInitialTransitions(self):        
        bottom = StateNode(self.text)
        for i in range(len(self.text)):
            bottom.addTransition(self.text[i],i,i, self.root)            
        self.root.sLink = bottom

    def buildTree(self):
        self.activeNode = self.root
        self.k =  0
        for i in range(len(self.text)):
            #self.show(); raw_input("[k:%s]" % self.k)
            self.processToken(i)
            self.findAndCanonizeNewActivePoint(i)

    def findAndCanonizeNewActivePoint(self, i):
        self.activeNode, self.k = self.canonize(self.activeNode, self.k, i)

    def processToken(self, i):
        state, k = self.activeNode, self.k
        
        oldr = self.root        
        endPoint, r = self.test_and_split(state, k, i-1, self.text[i])
        
        while not endPoint:
            r.addTransition(self.text[i], i, FarRight, StateNode(self.text))
            if (oldr != self.root):
                oldr.sLink = r
            oldr = r
            state, k = self.canonize(state.sLink, k, i-1)
            endPoint, r = self.test_and_split(state, k, i-1, self.text[i])                                          
        if oldr != self.root:
            oldr.sLink = state

        self.activeNode, self.k = state, k

    def test_and_split(self, state, k, p, token):
        if k <= p:
            nextch = self.text[k]
            bounds, state1 = state[nextch]
            if (token == self.text[(bounds.left + p - k + 1)]):
                return (true, state)
            else:
                r = StateNode(self.text)
                state.addTransition(self.text[bounds.left], bounds.left, bounds.left+p-k,   r)
                newLeft = bounds.left + p - k + 1
                r.addTransition(self.text[newLeft],  newLeft, bounds.right, state1)
                return (false, r)
        else:
            return (state.contains(token), state)

    def canonize(self, state, k, p):
        if p < k:
            return (state, k)
        else:
            bounds, state1 = state[self.text[k]]
            while bounds.width() <= p-k:
                k += bounds.width() + 1
                state = state1
                if k <= p:
                    bounds, state1 = state[self.text[k]]
            return (state, k)


    ## display methods #####################################
        
    def show(self, stream=None):
        out = stream or sys.stdout
        self.showStateNode(out, self.root, 0, "SuffixTree('%s')" % self.text)

    def slice(self, bounds):
        if bounds.right is FarRight:
            return self.text[bounds.left:]
        else:
            return self.text[bounds.left:bounds.right+1]
     
    def showStateNode(self, out, node, depth, label):
        out.write("    " * depth)
        out.write(label)
        if node.children():
            out.write(":\n")
        else:
            out.write("\n")
        for (bounds, child) in node.children():
            childLabel = self.slice(bounds)
            self.showStateNode(out, child, depth+1, childLabel)
            

if __name__=="__main__":
    SuffixTree("abcdefg").show()
    SuffixTree("mississippi").show()
