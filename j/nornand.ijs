NB. The 16 boolean operations, expressed as combinations of nand and nor.
NB. (for each table below, some lines have multiple formulations)
p =: 0 0 1 1
q =: 0 1 0 1
c =: assert NB. c for check


NB. the 16 boolean dyads, as combinations of NAND
NB. na is a named dyad to prevent accidental use of monadic *:
NB. (which is just an identity function for booleans)
na =: [: : *:
c  0 0 0 0  -: p (] na~@na na) q
c  0 0 0 1  -: p (na na na) q
c  0 0 1 0  -: p na~@([ na na) q
c  0 0 1 1  -: p (na na na~@[) q
c  0 1 0 0  -: p ((] na na) na (na na ])) q
c  0 1 0 1  -: p (na na na~@]) q
c  0 1 1 0  -: p (([ na na) na (] na na)) q
c  0 1 1 1  -: p na&(na~) q
c  1 0 0 0  -: p na~@na&(na~) q
c  1 0 0 1  -: p (([ na na) na~@na (] na na)) q
c  1 0 1 0  -: p (] na ]) q
c  1 0 1 1  -: p (] na na) q
c  1 1 0 0  -: p ([ na [) q
c  1 1 0 1  -: p ([ na na) q
c  1 1 1 0  -: p na q
c  1 1 1 1  -: p (] na (]na])) q


NB. the 16 boolean dyads, as combinations of NOR
nr =: [: : +:
c  0 0 0 0  -: p (] nr (]nr])) q
c  0 0 0 1  -: p nr&(nr~) q
c  0 0 1 0  -: p (] nr nr) q
c  0 0 1 1  -: p (nr nr ([nr[)) q
c  0 1 0 0  -: p ([ nr nr) q
c  0 1 0 1  -: p (nr nr (]nr])) q
c  0 1 1 0  -: p (([ nr nr) nr~@nr (] nr nr)) q
c  0 1 1 1  -: p (nr nr nr) q
c  1 0 0 0  -: p nr q
c  1 0 0 1  -: p (([ nr nr) nr (] nr nr)) q
c  1 0 1 0  -: p (] nr ]) q
c  1 0 1 1  -: p (([ nr nr) nr ([ nr nr)) q
c  1 1 0 0  -: p ([ nr [) q
c  1 1 0 1  -: p nr~@([ nr nr) q
c  1 1 1 0  -: p nr~@nr&(nr~) q
c  1 1 1 1  -: p (] nr~@nr nr~@]) q


NB. the 16 boolean dyads as combinations of NAND and NOR
c  0 0 0 0  -: p ([ nr na) q
c  0 0 0 1  -: p (na na na) q
c  0 0 1 0  -: p (] nr nr) q
c  0 0 1 1  -: p (na na ([na[)) q
c  0 1 0 0  -: p ([ nr nr) q
c  0 1 0 1  -: p (nr nr (]nr])) q
c  0 1 1 0  -: p (([ na na) na (] na na)) q
c  0 1 1 1  -: p (nr nr nr) q
c  1 0 0 0  -: p nr q
c  1 0 0 1  -: p (([ nr nr) nr (] nr nr)) q
c  1 0 1 0  -: p (] na ]) q
c  1 0 1 1  -: p (] na na) q
c  1 1 0 0  -: p ([ na [) q
c  1 1 0 1  -: p ([ na na) q
c  1 1 1 0  -: p na q
c  1 1 1 1  -: p (] na nr) q
