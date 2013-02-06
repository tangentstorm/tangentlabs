# combinatory wheel system for lotteries
import unittest

## main logic  ##############################

def even(n):
    return n % 2 == 0

def half(n):
    return (n/2) if even(n) else (n+1)/2

def addends(total, howMany):
    "generates all combinations of (howMany) numbers that sum to (total)"
    if howMany == 1:
        yield (total,)
    else:
        start = total -1
        end = half(total)
        for x in range(start, end-1, -1):
            # strip x,x but keep x,(y+z==x)
            if howMany == 2 and x == total-x:
                continue
            else:
                for others in addends(total-x, howMany-1):
                    yield (x,) + others

def wheel(total, constant, howManyOthers=4):
    "generates all addends but with one constant number"
    sub = total - constant
    for row in addends(sub, howManyOthers):
        if constant in row: continue
        yield (constant,) + row
                
def printWheel(total, constant, howManyOthers=4):
    "prints output of wheel() as a tab-separated list"
    for row in wheel(total, constant, howManyOthers):
        print "\t".join([str(n) for n in row])


## test cases ###############################
                
class TestIt(unittest.TestCase):
    def testAddends(self):
        self.assertEquals(
            list(addends(9, 1)),
            [(9,)] )
        
        self.assertEquals(
            list(addends(9, 2)),
            [(8,1), (7,2), (6,3), (5,4)])

        # we don't want 5,5
        self.assertEquals(
            list(addends(10, 2)),
            [(9,1), (8,2), (7,3), (6,4)])

        self.assertEquals(
            list(addends(11, 3)),
            [(8, 2, 1), (7, 3, 1), (6, 4, 1), (6, 3, 2)])

    def testWheel(self):
        # here are all the ways to add up 4 numbers to make 20:
        self.assertEquals(
            list(addends(20,4)),
            [(14, 3, 2, 1),
             (13, 4, 2, 1),
             (12, 5, 2, 1),
             (12, 4, 3, 1),
             (11, 6, 2, 1),
             (11, 5, 3, 1),
             (10, 7, 2, 1),
             (10, 6, 3, 1),
             (10, 5, 4, 1),
             (10, 5, 3, 2)])

        # so to make 30 and always use one 10, we want
        # the same list minus the rows that already had a 10:
        self.assertEquals(            
            list(wheel(30,10,4)),
            [(10, 14, 3, 2, 1),
             (10, 13, 4, 2, 1),
             (10, 12, 5, 2, 1),
             (10, 12, 4, 3, 1),
             (10, 11, 6, 2, 1),
             (10, 11, 5, 3, 1)])
       
if __name__=="__main__":
    unittest.main()
