# http://stackoverflow.com/questions/5087754/is-it-possible-to-convert-this-recursive-solution-to-print-brackets-to-an-itera
# he gave us this:

def genBrackets(c):
    def genBracketsHelper(r,l,currentString):
        if l > r or r == -1 or l == -1:
            return
        if r == l and r == 0:
            print currentString
        genBracketsHelper(r,l-1, currentString + '<')
        genBracketsHelper(r-1,l, currentString + '>')
        return
    genBracketsHelper(c, c, '')



if True:
    def genBrackets(c):
        stack = [(c, c, '')]
        while stack:
            right, left, currentString = stack.pop()
            if left > right or right == -1 or left == -1:
                pass
            elif right == left and right == 0:
                print currentString
            else:
                stack.append((right, left-1, currentString + '<'))
                stack.append((right-1, left, currentString + '>'))



if True:

    def isValid(string):
        """
        True if and only if the string is balanced.
        """
        count = { '<': 0, '>':0 }
        for char in string:
            count[char] += 1
            if count['>'] > count['<']:
                return False # premature closure

        if count['<'] != count['>']:
            return False # unbalanced
        else:
            return True


    def genBrackets(c):
        """
        Generate every possible combination and test each one.
        """
        for i in range(0, 2**(c*2)):
            candidate = bin(i)[2:].zfill(8).replace('0','<').replace('1','>')
            if isValid(candidate):
                print candidate



genBrackets(4)
print "---"
genBracketsIteratively(4)




