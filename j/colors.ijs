NB. terminal colors

esc=: (27{a.),'[',]
clrscr =: (13 : 'esc"0 ''HJ''')
ccolor =: 'krgybmcywKRGYBMCYW'i.]
fg =: ((esc'0;'),([: ":30+ccolor),'m'"_)"0

echo (clrscr''),(fg'r'),'hello ',(fg'b'),'world',(fg'w')
