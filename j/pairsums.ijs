NB. Given a list of numbers, find pairs that sum to 8.

NB. 'where' takes two arrays with the same tally.
NB. it ravels (,) both arguments (converts to 1d)
NB. and then creates x[i] copies (#) of y[i].
where =: ([:,]) # ([:,[)

NB. 'pairs' creates a table (/~) of pairs (,"0)
NB. and then boxes each of the pairs (<"1) so
NB. that where operates on the boxed pairs.
pairs =: <"1 @ ,"0/~

(pairs where 8 = +/~) 1 2 3 4 5 6 8 4 99
