# math from strings

ZERO = ""

def sort(s):
    chars = [c for c in s]
    chars.sort()
    return "".join(chars)

def simplify(s):
    res = sort(s)
    while res.count("<>"):
        res = res.replace("<>", ZERO)
    return res

def negate(s):
    res = s
    res = res.replace(">",".")
    res = res.replace("<",">")
    res = res.replace(".", "<")
    return res

def isNegative(s):
    return s.startswith("<")

def absolute(s):
    return s.replace("<",">")

def pickSign(a,b, c):
    "fix the sign for multiplication and division"
    if isNegative(a) ^ isNegative(b): # xor
        return negate(c)
    return c

## arithmetic ##

def add(a, b):
    "a + b"
    return simplify(a + b)

def subtract(a, b):
    "a - b"
    return add(a, negate(b))
    
def multiply(a, b):
    "a * b"
    res = ZERO
    for each in b:
        res = add(res, absolute(a))
    return pickSign(a, b,  simplify(res))

def power(a, b):
    "a ** b"
    res = ">"
    assert not isNegative(b), "no negative powers at this time"
    for each in b:
        res = multiply(res, b)
    return res

def divide(a, b):
    "a / b, returns quotient and remainder"
    quotient = ZERO  
    remainder = absolute(a)
    chunkSize = absolute(b)
    while remainder >= chunkSize:
        quotient += ">"
        remainder = subtract(remainder, chunkSize)
    return pickSign(a, b, quotient), remainder

## tests ###

if __name__=="__main__":
    assert simplify("<>>") == ">"
    assert simplify(">><") == ">"
    assert negate("<>") == "><"
    two = ">>"
    four = ">>>>"
    eight = ">>>>>>>>"
    negative_two = "<<"
    negative_four = "<<<<"
    assert multiply(two,two) == four
    assert multiply(two,four) == eight
    assert multiply(negative_two, two) == negative_four
    assert multiply(ZERO, two) == ZERO
    assert divide(negative_four, two) == (negative_two, ZERO)
