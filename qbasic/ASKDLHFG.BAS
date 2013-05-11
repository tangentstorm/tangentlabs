OPEN "SHRINE.CEL" FOR INPUT AS #1
z = 0
DO UNTIL EOF(1))
 z = z + 1
 x$ = INPUT$(2, #1)
 IF x$ = char$(1) + char$(40) THEN PRINT z
LOOP UNTIL (EOF(1))
CLOSE #1

