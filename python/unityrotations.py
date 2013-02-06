
# trying to import from 3dsmax to unity
# i think the fix is some combination of rotating 180 degrees
# around some number of axes and scaling by -1 across some axes.
# that's 2^6=64 combinations. I'm just going to brute force it.
#
# what i'm doing here is generating the checklist.

for x in range(64):
    bits = tuple(int(digit) for digit in bin(x)[2:].zfill(6))
    test = (tuple(180 * i for i in bits[:3]) +
            tuple((1 if i == 0 else -1) for i in bits[3:]))
    print '%2s:' % x,
    print ' '.join("%4d" % x for x in test), ":"
    


