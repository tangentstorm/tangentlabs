# example codility problem pointed out by my friend eusebio.
# my score for this one is here:
# https://app.codility.com/demo/results/training7QTD65-X2S/
#
# (that version had a small bug in build_fibs that caused it
# to omit one value when N was very small, hence the 2
# failing tests... but you can't correct the answer after
# submitting there...)

def build_fibs(N=100000):
    res=[1,2,3] + 1000*[0]
    i=1; j=1; k=2; x=3
    while k<N:
        i,j=j,k
        k=i+j
        res[x]=k
        x+=1
    return res[:x]

def find_pads(A):
    """returns the indices of the pads (&A in K / I.A in j)"""
    j=0; res = [0]*len(A)
    for i,v in enumerate(A):
        if v:
            res[j] = i
            j+=1
    return res[:j]


def solution(A, F=None):
    N = len(A)
    P = find_pads(A)         # P: position of each pad in A
    F = F or build_fibs(N)   # F: fibonacci numbers up to N
    print(F)
    # for each pad, we want to know whether we can reach
    # the end, and whether we can reach the pad from the start.
    def try_jumps(starts, best):
        """
        starts: list of start positions
        best: (mutable) map of positions -> shortest paths
        returns the list of newly reached positions
        """
        new = []
        # try big jumps first just in case we reach N
        for s in reversed(sorted(starts)):
            for jump in reversed(F):
                p = s + jump
                if p > N: continue # jumped too far
                if p == N or A[p]: # is there a pad at p?
                    jumps = best[s] + 1
                    if p in best:
                        if jumps < best[p]:
                            best[p] = jumps
                        else:
                            pass # path not shorter
                    else:
                        best[p] = jumps
                        new.append(p)
                else:
                    pass # landed in water
        return new

    s = [-1]    # starting positions
    best = {-1:0}  # known world (pos->num jumps)
    while s and N not in best:
        s = try_jumps(s, best)
    return best.get(N,-1)


if __name__=="__main__":
    print(solution([1,1]))
