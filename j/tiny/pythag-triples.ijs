NB. find all the pythagorean triples with sides less than n (ignoring multiples)
~.((%+./)@/:~)@(,+/&.:*:)"1>:($#:I.@:(=<.)@,)+&.*:/~1+i.  n=.20
NB.   3  4  5
NB.   5 12 13
NB.   8 15 17

Note'explanation. [data flows from the right (bottom) to left (top)]'
~.          → nub (unique items)
(%+./)      → divide by least common factor (so 6 8 10 becomes 3 4 5)
@           → function composition
/:~         → sort (so 4 3 5 becomes 3 4 5)
(,+/&.:*:)  → append the square root of the sum of the squares...
"1          → ... for each row.
>:          → add one to each value
($ #:       → use shape of 2d table as numeric base (so indices become coordinates)
   I.@:     → return the indices of 1 bits
   (=<.)    → set items to 1 when integer (equal to floor), else 0
        @,) → unravel the 2d table to a 1d vector
+&.*:/~     → square root of sum of squares table
1+i.n=.20   → the range 1 2 3 ... 19 20
)