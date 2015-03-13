/ texas holdem hand database
/ -----------------------------------------------------


/ helper routines
syms: {`$ x,' $string each til y}
syms["c";4] / -> `c0`c1`c2`c3

{reverse ,\[til x]}


/ {r:til x; r:,/[r,\:/:r]; r[where r[;0]<r[;1]]} [4]
asc r @ where </'[r]

/ -----------------------------------------------------

/ primitive concepts (single columns)
ranks: ([]r:"23456789TJQKA")
suits: ([]s:"cdhs")

/ map each card to number (in implicit column 'i')
cards: select c:(`$r,'s), r, s from ranks cross suits
deck: select c from cards

/ views for each suit
suit: {cards[where cards.s=x]}
C::suit"c"; D::suit"d"; H::suit"h"; S::suit"s"

/ hole cards
hc: select from cross/[syms["h";2] xcol\: deck] where h0<h1
