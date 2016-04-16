

do =: verb define
  NB. allow multiple statements per line, separated by ]:
  for_cmd. <;._1 ']:' ; ;: y do. ".;> cmd end.
)
setg=: dyad define
  ":x,'=:',(5!:6)<'y'  NB. set global using parenthesized repr
)
A=:1 :'if.0 do.u y(to force verb result)else.(5!:1)<''u''end.'

team =: dyad : 'x `:0 y' "0 _

NB. compose gerunds
compose =: ([:`''),[,]
toverb  =: `:6
cheq (compose/(+8:)`(*3:)`(^2:)) toverb 5
83
)

NB. from jpjacobs in #jsoftware (reconstructed from memory)
squeeze=:((#~(~:1:))@$$,)

NB. number of bits in a number
nbits =: [:>.2^.>:
cheq nbits i.33
0 1 2 2 3 3 3 3 4 4 4 4 4 4 4 4 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 5 6
)

NB. next power of two:
npow2 =: >.&.(2^.])@>:
cheq npow2 i.33
1 2 4 4 8 8 8 8 16 16 16 16 16 16 16 16 32 32 32 32 32 32 32 32 32 32 32 32 32 32 32 32 64
)

NB. div/mod: integer division
div=:([-|~)%]
mod=:|~

NB. shift/rotate operators
shl=:[: :(    33 b.~ )
shr=:[: :(-@] 33 b. [)
asl=:[: :(    34 b.~ )  NB. arithmetic shift left (keep sign)
asr=:[: :(-@] 34 b. [)
rol=:[: :(    32 b.~ )
ror=:[: :(-@] 32 b. [)

bin=:'01'{~(64#2)&#:
bix=:'.x'{~(64#2)&#:

gos=: verb define
  NB. gosper''s hack: next highest permutation of the bits
  lo =. (*.bw -) y
  lf =. y + lo
  cb =. y ~:bw lf
  lf +.bw (cb div lo) shr 2
)
