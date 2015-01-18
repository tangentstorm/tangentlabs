NB. program to calculate musical scales

tones=:(tones)=:s:chopstring tones=:'C Db D Eb E F Gb G Ab A Bb B'
'ionian dorian phrygian lydian mixolydian aoelian locrian'=:i.7
cmaj =: C,D,E,F,G,A,B,C
major=: 12|2 -~/\ tones i.cmaj
scale=:verb :('0 scale y'; ':'; '(12|0,+/\ x|. major) { (tones i. y) |. tones')

assert (dorian scale G) -: G,A,Bb,C,D,E,F,G

