NB. ansi escape codes for color, etc.

esc =: u:27
reset =: esc,'[0m'
clrscr =: esc,'[H',esc,'[J'

NB. cwcolorb → c b (color, bold) where (c e. i.8) ∧ (b e. 0 1)
cwcolorb  =. 8 (|,>:) 'krgybmcwKRGYBMCW' i. ]
ansibold =. (esc,'[1m')               NB. noun
ansifg   =. (esc,'[3','m',~ ":@{.)    NB. verb (y e. i.8)

NB. older ansi style fg/bg codes:
fga =. [: (reset, (esc, '[3','m',~ ":@{.), ,@(ansibold #~"1 0 }.)) cwcolorb
bga =. [: (reset, (esc, '[4','m',~ ":@{.), ,@(ansibold #~"1 0 }.)) cwcolorb

NB. xterm 256-color codes
NB. these work the same for the first 16 colors, but have the advantage
NB. but do not require sending the "reset" sequence when toggling bold.
NB. (the "reset" code resets both the foreground and background)
NB. Most modern terminals seem to support 256 colors.
fgn=: esc, '[38;5;', 'm',~ ":
bgn=: esc, '[48;5;', 'm',~ ":
cwc=: [: [:^:(16=]) 'krgybmcwKRGYBMCW' i. ]
istxt=. 131072 2048 2 e.~ 3!:0
fg=: ([: fgn cwc^:istxt) f.
bg=: ([: bgn cwc^:istxt) f.
