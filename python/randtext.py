"""
[2008.0925 08:56PM] Stereo Stenanography


"""

import random
import sys
import copy

MESSAGE = "STEREOSTENANOGRAPHY"

def randchar():
    return "abcdefghijklmnopqrstuvwxyz"[random.randint(0,25)]


def mismatch(leftChar=None):
    left = leftChar or randchar()
    # make sure they're not the same:
    right = randchar()
    while right == left:
        right = randchar()
    return left, right







def first_attempt_gen(message):
    '''
    left/right "backgrounds" are completely random.
    the chars appear in exact same spot each time.
    '''
    i = 0
    while i < len(message):

        if random.randint(1,100) < 10 :
            yield message[i], message[i]
            i +=1

        else:
            yield mismatch()

def first_attempt(msg, w=20, h=10):

    pairgen = first_attempt_gen(msg)

    for y in range(h):

        lLine, rLine = [],[]

        for x in range(w):

            try:
                lChar, rChar = pairgen.next()
            except StopIteration:
                lChar, rChar = randpair()

            lLine.append(lChar)
            rLine.append(rChar)

        print '    ', ''.join(lLine), '  ', ''.join(rLine)


##############################################################
        

def second_attempt(word, w, h):
    """
    let's start with two grids that are
    exactly the same:
    """
    lField = [[randchar() for x in range(w)] for y in range(h)]
    rField = copy.deepcopy(lField)


    def putchar(x,y,c,offset=2):
        lField[y][x]=c
        rField[y][x+offset]=c

    putchar(w/2-1, 0, '[', 0)
    putchar(w/2,   0, '*', 0)
    putchar(w/2+1, 0, ']', 0)

    def putword(x,y,word,offset=2):
        for i, c in enumerate(word):
            putchar(x=x + i, y=y, c=c, offset=offset)

    putword(2,2, 'secret', offset=1)
    putword(3,3, 'message', offset=2)
    putword(2,4, 'from', offset=2)
    putword(3,6, 'withoutane.com', offset=2)

    gutter = '   '
    indent = '    '

    print
    print
    for y in range(h):
        print ''.join([indent, ''.join(lField[y]), gutter, ''.join(rField[y])])
    print
    print
    

second_attempt(MESSAGE, 25, 10)
