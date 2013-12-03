NB. a J word to generate square bitmaps representing
NB. the binary representation of a number.

NB. number of bits needed to represent y
nbits =: (2: >. [: >. 2:^.])   NB. max(2, ceil(log2(n)))

NB. dim : smallest square shape to hold y cells.
NB. example: dim 14 -> 4 4.
dim =: (2: $ [: >. %:)         NB. dup(ceil(sqrt n))

NB. lpz : "left pad with zeros". lpz 1 2 -> 0 0 0 1 2
NB. lpz =: (4 : '|. x $!.0 |. y')
lpz =: -@[ {. ]            NB. thanks to b_jonas

NB. sqb : arrange binary representation of y into a square matrix
sqb =: (3 : '(dim nbits y) $ (*/ dim nbits y) lpz #: y' )

NB. bmp : draw a bitmap
bmp =: '.#' {~ ]

NB. each =: &.>

(bmp @ sqb) each i.8

NB. output
NB. +--+--+--+--+--+--+--+--+
NB. |..|..|..|..|.#|.#|.#|.#|
NB. |..|.#|#.|##|..|.#|#.|##|
NB. +--+--+--+--+--+--+--+--+

