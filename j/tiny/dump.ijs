dump=: [: > [: ([: < '[',']',~ [: > ([,', ',])&.>/)"1 ^:(#@$) <@:":"0

Note 'dump'

Generates a linear string representation of an array for export.

Examples:

        dump each 1 ; (,2); 3 3; (2 2 $ 4); 2 2 2 $ 5
    ┌─┬───┬──────┬────────────────┬────────────────────────────────────┐
    │1│[2]│[3, 3]│[[4, 4], [4, 4]]│[[[5, 5], [5, 5]], [[5, 5], [5, 5]]]│
    └─┴───┴──────┴────────────────┴────────────────────────────────────┘

       dump 2 2 $ s:' the quick brown fox'
    [[the, quick], [brown, fox]]

It builds the string from the bottom up, first by boxing all the atoms
in the array, and then repeatedly converting each rank 1 subarray into
a boxed string (which is a scalar, thus reducing the total rank by 1).
This gives a single boxed string, which is then unboxed to produce the
final result.

)