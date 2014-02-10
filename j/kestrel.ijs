
NB. == registers and ram ===

'U V W X Y Z' =: i. 6   NB. these are indices into the 'regs' array

reset =: 3 : 0
  ram   =: 32 $ 0         NB. toy ram for testing
  regs  =: 6 $ 0          NB. the registers for the stack
  P     =: 0              NB. stores the program counter
  I     =: 0              NB. stores the actual instruction
)

NB. shorthand version of the above, for IRC:
reset  =: 3 : ('ram=:32$0'; 'regs=:6$0'; 'P=:0'; 'I=:0')

NB. -- queries -----------------
show   =: 3 : ('I;P;regs;ram')
reg    =: 3 : ('y { regs')                            NB. query register: reg Z

NB. -- cpu internals -----------
incP   =: 1 : ('u y' ; 'P=:P+2')                      NB. adverb to increment P afterward
wordAt =: 3 : (' +/ 1 256 * (y + 0 1) { ram ')        NB. fetch a 2 byte word from ram
nextI  =: 3 : ('I =: wordAt P') incP                  NB. fetch instruction
step   =: 3 : ('nextI _'; 'ops @. I _')               NB. fetch instruction and perform it
steps  =: 4 : ('reset _'; 'ram =: y'; 'step^:x _')    NB. reset and run x steps against ram y

bw     =: 1 : ('u &.:((16#2)&#:)')                    NB. bitwise adverb (for boolean dyads only)
bwAnd  =: *: bw                                       NB. bitwise and
bwShl  =: 33 b.                                       NB. shift bits in y left x spaces

NB. -- instruction set ---------
NOP  =: [
LIT  =: 3 : ('regs =: (}:regs), wordAt P') incP
FWM  =: 3 : ('regs =: (wordAt Z{regs) Z } regs') incP
ops =: NOP`LIT`FWM

NB. TODO: s1 s2 s3 s4 =: (12 8 4 0) SHL (61440 3840 240 15) AND 4$I


test =: 3 : 0
 a =. assert
 a (256=reg Z)[ 1 steps 1 0, 0 1, 0 0            NB. LIT 256 NOP
 a (512=reg Z)[ 2 steps 1 0, 6 0, 2 0, 0 2       NB. LIT 6 FWM 512
 'all tests passed'
)
test''
