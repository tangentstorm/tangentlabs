-- from an online problem where at each step, you have to
-- turn one of n concentric dials on a combination lock.
-- each dial points at a number in [0..2^k-1] and points to 0 initially.
-- turning dial d also turns dials [d+1..n-1]. given a list of (dial,steps)
-- pairs, track the position of each dial's pointer.

bit x = if x then 1 else 0
zsum = foldl1 (zipWith(+))
turn n k ts = map (`mod`(2^k))$ zsum [[s*bit(x>=d-1)|x<-[0..n-1]]|(d,s)<-ts]
result = turn 4 6 [(3,2),(2,1)]
main = print result
