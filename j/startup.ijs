NB. common words and customizations to the J environment.
NB. ============================================================
cocurrent'z'


cc =: cocurrent :: coname f.
module =: cocurrent
import =: coinsert [ require

immex =: [:(9!:29)1: [9!:27 NB. schedule y:str for immediate execution

doAt=: 2 : '(u n{y) n } y NB. apply u at indices given by n'

ord  =: a.i.]
chr  =: ord^:_1
ctrl =: (_64 + ])&.ord  NB. ASCII control characters

setg=: dyad define
  ":x,'=:',(5!:6)<'y'  NB. set global using parenthesized repr
)


NB. x? m A y : accessor for array m
NB. ------------------------------------------------------------
NB. If J is a list, then (j=:'J'A) defines a verb that can
NB. query and/or modify that array according to the following rules:
NB.
NB.           (j'') -: J
NB.           (j y) -: y{J     (y is a scalar index of J)
NB.         (x j y) ⇔ (J=:x(y)}J)
NB.
A=:1 :(f;':';'".m,''=:a'' [ a=.x ', f=.'(y})^:(*#y)a=.m~')

NB. G and P (get/put) are simpler but less versatile.
G=:1 :'m~[y'
P=:1 :'m setg y'

B=:1 :'<m[y'  NB. 'm V' is a verb that returns <m (short for '(<m)"_')
S=:1 :'s:<m'  NB. 'm S' produces a symbol from m (a string).
getcwd=:1!:43 NB. same as 'jcwdpath' but easier for me to remember.
chdir =:1!:44 NB.


NB. enum y : define ordinal constants from names in string y
NB. ------------------------------------------------------------
NB. ex: (enum'a b c' ⇔ 'a b c'=:i.3)
enum =: [: ". [: ;"1 [: (,. '=:'B ,. ((<@":)"0)@i.@#) ;:


NB. hooks for transient or os-specific config changes.
NB. ------------------------------------------------------------

(3 : 0)''
  NB. include scratch.ijs if it exists
  NB. (so i have a place to put work-in progress/debug code to run at startup)
  if. fexist '~/l/j/scratch.ijs' do. load '~/l/j/scratch.ijs' end.
)

(3 : 0) ^:( UNAME-:'FreeBSD' )
  load 'freebsd.ijs'
)
