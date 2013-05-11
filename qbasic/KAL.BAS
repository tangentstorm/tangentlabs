SCREEN 12
WHILE INKEY$ = ""
x = INT(RND * 640)
y = INT(RND * 350)
c = INT(RND * 8) + 8
CIRCLE (x, y), INT(RND * 240), c
'IF INT(RND * 2) > .5 THEN PAINT (x, y), c, c
WEND
END

