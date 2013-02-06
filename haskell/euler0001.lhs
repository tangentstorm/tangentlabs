

"""
If we list all the natural numbers below 10 that are multiples of 3 or
5, we get 3, 5, 6 and 9. The sum of these multiples is 23.

Find the sum of all the multiples of 3 or 5 below 1000.
"""
-- http://projecteuler.net/index.php?section=problems&id=1m


> x % y = mod x y
> main = print $ sum multiples where
>      multiples = filter (\x -> (0 == x % 5) || (0 == x % 3)) [1..999]

