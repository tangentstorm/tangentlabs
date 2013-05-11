' Michal Wallace
' Four LEtter Words

Base$ = ""
Word$ = ""
Done$ = ""
INPUT "String: ", Base$
Base$ = Base$ + " "
FOR A = 1 TO LEN(Base$)
 M$ = MID$(Base$, A, 1)
 IF M$ = " " THEN
  IF LEN(Word$) = 4 THEN
   Done$ = Done$ + "****" + " "
  ELSE
   Done$ = Done$ + Word$ + " "
  END IF
  Word$ = ""
 ELSE
  Word$ = Word$ + M$
 END IF
NEXT A
PRINT "STARTING STRING :"; Base$
PRINT "CONVERTED STRING:"; Done$


