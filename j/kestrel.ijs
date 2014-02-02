) 'U V W X Y Z' =: i. 6   NB. these are indices into the 'regs' array

reset =: 3 : 0
  ram   =: 32 $ 0         NB. toy ram for testing
  regs  =: 6 $ 0          NB. the registers for the stack
  P     =: 0              NB. stores the program counter
  I     =: 0              NB. stores the actual instruction
)
NB. shorthand version of the above, for IRC:
) reset  =: 3 : ('ram=:32$0'; 'regs=:6$0'; 'P=:0'; 'I=:0')

) wordAt =: 3 : (' +/ 1 256 * (y + 0 1) { ram ')
) incp   =: 3 : ('P =: P + 2')
) nextI  =: 3 : ('I =: wordAt P'; 'incp _')
) step   =: 3 : ('nextI _'; 'ops @. I _')
) show   =: 3 : 'I;P;regs;ram'
) bw =: 1 : 'u &.:((16#2)&#:)'  NB. bitwise adverb
) bwAnd  =: *: bw
) bwShl  =: 33 b.
) NOP  =: [
) LIT  =: 3 : ('regs =: (}:regs), wordAt P'; 'incp _')
) FWM  =: 3 : ('regs =: (wordAt Z{regs) Z } regs'; 'incp _')
) ops =: NOP`LIT`FWM

s1 s2 s3 s4 =: (12 8 4 0) SHL (61440 3840 240 15) AND 4$I

) (ram =: 1 0 0 1 0 0) [ (reset _ ) NB. LIT 256 NOP
) (ram =: 1 0,6 0,2 0, 0 1) [ (reset _ ) NB. LIT 3 FWM 256
