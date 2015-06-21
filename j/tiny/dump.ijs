dump=:((_2}.])@,@:(('[','], ',~":)"1)^:(0<#@$))`":@.(0=#@$)

Note 'dump'

Generates a one-line string representation of an array, for export.

Examples:

       dump each 1 ; (,2); 3 3; (2 2 $ 4)
    ┌─┬───┬─────┬────────────┐
    │1│[2]│[3 3]│[4 4], [4 4]│
    └─┴───┴─────┴────────────┘

Sadly, it does not yet work correctly when the array has a rank greater than 2:

       dump 2 2 2 $ 5
    [5 5], [5 5], [5 5], [5 5]

There should be an extra layer of braces around it. The problem is
that i want to dispatch recursively based on the rank of the input,
but things get messy when a rank 0 int becomes a rank 1 string.

)