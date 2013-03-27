# -*- coding: utf-8 -*-
"""
colliding disks
"""

import numpy as np
import numpy.random as nr

n = 10 # number of discs
w = 100 # width
h = 100 # height
r = 1   # radius

# create  n random x,y pairs
x = nr.random(n) * w
y = nr.random(n) * h

# loop indices for all pairs in range(n)
i, j = np.indices((n, n))

# calculate the distance between each combination of points:
d = np.sqrt(( x[i] - x[j]) ** 2 + ( y[i] - y[j]) ** 2)

# now find all the colliding pairs
# this is simply an n*n array of values:
# 0 indicates no collision, 1 indicates a collision
cpr = (d <= r) * 1  # the *1 casts boolean results of <= to [0,1]

# remove redundant information:
# forall circles i,j, if i collides with j then j collides with i
# forall circles i,j, if i = j then i collides with j.
# To avoid all this duplicate data, we will fill the upper right hand
# triangle of the n*n array of pairs with zeros:
cpr = np.tril(cpr, -1)

# collision report:
cc = sum(cpr) # collision count
if cc == 1: print "there was 1 collision"
else: print "there were %i collisions." % cc 

