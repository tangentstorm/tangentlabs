
'Michal Wallace
'Arabic to english numbers

ARABIC$ = ""
ARAB$ = ""
ENGLISH$ = ""
DIM NUM$(9)
 NUM$(1) = "ONE"
 NUM$(2) = "TWO"
 NUM$(3) = "THREE"
 NUM$(4) = "FOUR"
 NUM$(5) = "FIVE"
 NUM$(6) = "SIX"
 NUM$(7) = "SEVEN"
 NUM$(8) = "EIGHT"
 NUM$(9) = "NINE"
DIM NUM2$(9)
 NUM2$(1) = "TEN"
 NUM2$(2) = "TWENTY"
 NUM2$(3) = "THIRTY"
 NUM2$(4) = "FOURTY"
 NUM2$(5) = "FIFTY"
 NUM2$(6) = "SIXTY"
 NUM2$(7) = "SEVENTY"
 NUM2$(8) = "EIGHTY"
 NUM2$(9) = "NINETY"
DIM NUM3$(10)
 NUM3$(1) = "TEN"
 NUM3$(1) = "ELEVEN"
 NUM3$(2) = "TWELVE"
 NUM3$(3) = "THIRTEEN"
 NUM3$(4) = "FOURTEEN"
 NUM3$(5) = "FIFTEEN"
 NUM3$(6) = "SIXTEEN"
 NUM3$(7) = "SEVENTEEN"
 NUM3$(8) = "EIGHTEEN"
 NUM3$(9) = "NINETEEN"

INPUT "STARTING NUMBER: ", ARAB$
ARABIC$ = ARAB$
WHILE LEN(ARABIC$) MOD 3 <> 0
 ARABIC$ = "0" + ARABIC$
WEND
FOR A = 1 TO LEN(ARABIC$) STEP 3
 M$ = MID$(ARABIC$, A, 3)
   IF (MID$(M$, 1, 1) <> " ") AND (MID$(M$, 1, 1) <> "0") THEN
     ENGLISH$ = ENGLISH$ + NUM$(VAL(MID$(M$, 1, 1))) + " HUNDRED "
   END IF
   IF (MID$(M$, 2, 1) <> " ") AND (MID$(M$, 2, 1) <> "0") AND (MID$(M$, 2, 1) <> "1") THEN
     ENGLISH$ = ENGLISH$ + NUM2$(VAL(MID$(M$, 2, 1))) + " "
   END IF
   IF (MID$(M$, 3, 1) <> " ") AND (MID$(M$, 3, 1) <> "0") AND (MID$(M$, 2, 1) <> "1") THEN
     ENGLISH$ = ENGLISH$ + NUM$(VAL(MID$(M$, 3, 1))) + " "
   END IF
   IF MID$(M$, 2, 1) = "1" THEN ENGLISH$ = ENGLISH$ + NUM3$(VAL(MID$(M$, 3, 1))) + " "
 IF (LEN(ARABIC$) - A = 5) AND (M$ <> "000") THEN ENGLISH$ = ENGLISH$ + "THOUSAND "
 IF LEN(ARABIC$) - A = 8 THEN ENGLISH$ = ENGLISH$ + "MILLION "
NEXT A
PRINT "ARABIC : "; ARAB$
PRINT "ENGLISH: "; ENGLISH$
END

