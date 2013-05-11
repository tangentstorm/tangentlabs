DECLARE SUB label (x!, y!, s$)
'Michal Wallace
'The House Assignment


DECLARE SUB hline (x1, y1, x2, y2)
DECLARE SUB dvline (x1, y1, x2, y2)

SCREEN 12
LINE (99, 39)-(601, 451), 2, BF

'Main Outline
CALL dvline(360, 50, 590, 280)
CALL dvline(590, 280, 590, 320)
CALL dvline(590, 320, 560, 350)
CALL dvline(560, 350, 560, 390)
CALL dvline(560, 390, 540, 410)
CALL dvline(490, 410, 460, 380)
CALL dvline(460, 380, 460, 370)
CALL dvline(460, 370, 440, 350)
CALL dvline(440, 350, 420, 370)
CALL dvline(310, 370, 290, 350)
CALL dvline(290, 350, 270, 370)
CALL dvline(270, 370, 270, 380) ' this is the vertical line left of garden
CALL dvline(270, 380, 240, 410)
CALL dvline(190, 410, 170, 390)
CALL dvline(170, 390, 170, 350)
CALL dvline(170, 350, 130, 310)
CALL dvline(130, 310, 140, 300)
CALL dvline(140, 300, 110, 270)
CALL dvline(110, 270, 110, 140)
CALL dvline(110, 140, 130, 120)
CALL dvline(130, 120, 130, 80)
CALL dvline(130, 80, 160, 50)
CALL hline(160, 50, 360, 50)
CALL hline(540, 410, 490, 410)
CALL hline(420, 370, 310, 370)
CALL hline(240, 410, 190, 410)
'palette 7, (
PAINT (160, 55), 7, 0

LOCATE 1, 25: PRINT "Michal Wallace - MW5FP.Bas"
LINE (0, 2 * 16 - 1)-(80, 2 * 16 - 1), 7
LOCATE 3, 1: PRINT "Key"
LINE (0, 3 * 16 - 1)-(80, 3 * 16 - 1), 7
LOCATE 4, 1: PRINT "C = Closet"
LOCATE 5, 1: PRINT "B = BathRm"



'Pool
DRAW "c1 bm390,60 d10 f90 r90 e10 u60 h40 l140 g10 br1 p9,1"
CALL label(480, 85, "Pool")

'Patio
DRAW "c0 bm481,170 r80 f30 d80 h110 r10 bd1 p6,0"
CALL label(535, 200, "Patio")

'Gardens
DRAW "c0bm250,410 f30 r30 h20 e10 r30 e10 u10 h10 l20 h20 g10 d10 g30 br p10,0"
DRAW "c0bm480,410 g30 l30 e20 h10 l30 h10 u10 e10 r20 e20 f10 d10 f30 bl p10,0"

'Atrium
DRAW "c0 bm200,200 e50 r100 f40 g30 d30 f20 d10 g40 l80 h60 u60 bf10 p2,0"
CALL dvline(200, 200, 250, 150)
CALL dvline(350, 150, 390, 190)
CALL dvline(390, 190, 360, 220)
CALL dvline(360, 220, 360, 250)
CALL dvline(360, 250, 380, 270)
CALL dvline(380, 270, 380, 280)
CALL dvline(380, 280, 340, 320)
CALL dvline(260, 320, 200, 260)
CALL dvline(200, 260, 200, 200)
CALL hline(250, 150, 350, 150)
CALL hline(340, 320, 260, 320)
CALL label(270, 220, "Atrium")

'Garage
CALL dvline(170, 350, 220, 300)
CALL dvline(220, 300, 280, 360)
CALL label(196, 360, "Garage")

'Bedroom
CALL dvline(140, 300, 180, 260)
CALL dvline(180, 260, 210, 290)
CALL label(160, 300, "Bed")

'Study
CALL dvline(180, 260, 180, 240)
CALL dvline(180, 220, 180, 170)
CALL dvline(130, 120, 140, 130)
CALL dvline(150, 140, 190, 180)
CALL label(125, 200, "Study")

'Master Bedroom
CALL dvline(190, 180, 210, 160)
CALL dvline(220, 150, 240, 130)
CALL dvline(240, 130, 240, 51)
CALL dvline(240, 50, 220, 70)
CALL dvline(200, 90, 210, 80)
CALL dvline(160, 50, 180, 70)
CALL dvline(190, 80, 210, 100)
CALL dvline(220, 110, 240, 130)
CALL label(150, 100, "Master")
CALL label(160, 120, "Bed")
CALL label(195, 60, "C")
CALL label(220, 85, "B")

'Library
CALL hline(240, 130, 280, 130)
CALL dvline(360, 130, 400, 90)
CALL hline(310, 130, 390, 130)
CALL hline(210, 50, 360, 50)
CALL label(270, 80, "Library")

'Game room
CALL dvline(351, 131, 370, 150)
CALL dvline(390, 100, 390, 110)
CALL dvline(390, 120, 390, 129)
CALL dvline(390, 131, 390, 140)
CALL dvline(390, 150, 390, 170)
CALL dvline(390, 170, 380, 160)
CALL dvline(400, 180, 420, 200)
CALL dvline(410, 190, 440, 160)
CALL dvline(440, 160, 440, 130)
CALL label(377, 113, "C")
CALL label(375, 137, "B")
CALL label(400, 123, "Game")
CALL label(400, 140, "Room")

'Guest Bedroom
CALL dvline(430, 210, 450, 230)
CALL dvline(480, 230, 510, 200)
CALL hline(450, 230, 480, 230)
CALL hline(440, 160, 450, 160)
CALL hline(460, 160, 470, 160)
CALL label(445, 145, "C")
CALL label(430, 183, "Guest")
CALL label(450, 200, "Bed")

'Closet
CALL dvline(370, 230, 400, 200)
CALL dvline(400, 200, 440, 240)
CALL dvline(440, 240, 440, 250)
CALL dvline(380, 250, 370, 240)
CALL dvline(370, 240, 370, 230)
CALL hline(440, 250, 380, 250)
CALL label(380, 230, "Closet")

'Living room
CALL label(440, 263, "Living")
CALL label(450, 280, "Room")

'Kitchen
CALL dvline(570, 260, 550, 280)
CALL dvline(540, 290, 520, 310)
CALL dvline(520, 310, 540, 330)
CALL dvline(550, 340, 560, 350)
CALL label(531, 302, "Kitchen")

'Dining Room
CALL dvline(430, 340, 440, 350)
CALL dvline(430, 340, 440, 330)
CALL dvline(450, 320, 460, 310)
CALL hline(460, 310, 490, 310)
CALL hline(500, 310, 520, 310)
CALL label(470, 333, "Dining")
CALL label(480, 350, "Room")

'Porch
CALL dvline(290, 350, 300, 340)
CALL hline(300, 340, 340, 340)
CALL hline(380, 340, 430, 340)
CALL label(340, 350, "Porch")

SUB dvline (x1, y1, x2, y2)
 LINE (x1 - 1, y1)-(x2 - 1, y2), 0
 LINE (x1, y1)-(x2, y2), 15
 LINE (x1 + 1, y1)-(x2 + 1, y2), 0
END SUB

SUB hline (x1, y1, x2, y2)
 LINE (x1, y1 - 1)-(x2, y2 - 1), 0
 LINE (x1, y1)-(x2, y2), 15
 LINE (x1, y1 + 1)-(x2, y2 + 1), 0
END SUB

SUB label (x, y, s$)
 LOCATE 1, 1
 PRINT s$
 DIM wrd(64, 16)
 DIM wrd2(64, 16)
 GET (0, 0)-(64, 16), wrd
 PUT (0, 0), wrd, PRESET
 GET (0, 0)-(64, 16), wrd2
 PUT (0, 0), wrd2, XOR
 PUT (x, y), wrd2, AND
 PUT (x, y), wrd, XOR
END SUB

