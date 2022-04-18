NB. this was a start on an alternative module system for j.
NB. it would be nice to both 'require' and 'coinsert'
NB. simultaneously, and that is what 'import' did... but
NB. it also meant you had to set up your environment in a
NB. non-standard way to even use the code, so... meh.
NB.
NB. this is mostly a historical artefact and not something
NB. you should actually use.
NB.
NB. there are also some miscellaneous other general purpose
NB. words that I thought would be nice standard verbs.

cc =: cocurrent :: coname f.
module =: cocurrent

NB. TODO: fix this so it can use any directory on the path...
import =: 3 : 0
  for_name. ;: y do.
    if. fexist modpath=.'~syn/',(>name),'.ijs' do. require modpath
    else. require name end.
    coinsert name
  end.
)


immex =: [:(9!:29)1: [9!:27 NB. schedule y:str for immediate execution


doAt=: 2 : '(u n{y) n } y NB. apply u at indices given by n'

OK   =: 0 0 $0
ok   =: OK"_


NB. install folder if it isnt there,
NB. TODO: make this a github module
{{ if. -. (<'syn') e. 0{"1 UserFolders_j_
   do. UserFolders_j_=:UserFolders_j_,'syn';jpath'~/ver/syndir' end.
}}''



NB. enum y : define ordinal constants from names in string y
NB. ------------------------------------------------------------
NB. ex: (enum'a b c' ⇔ 'a b c'=:i.3)
enum =: [: ". [: ;"1 [: (,. '=:'B ,. ((<@":)"0)@i.@#) ;:

NB. m args : creates a gerund containing m verbs
NB. verb i fetches item i from the y argument
NB. ------------------------------------------------------------
args =: adverb define
  r=.>a: for_i. i.m do. r=.r`([:>i{]) end.
)
'`a b c d' =: 4 args



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
setg=: dyad define
  ".x,'=:',(5!:6)<'y'  NB. set global using parenthesized repr
)
G=:1 :'m~[y'
P=:1 :'m setg y'

B=:1 :'<m[y'  NB. 'm V' is a verb that returns <m (short for '(<m)"_')
S=:1 :'s:<m'  NB. 'm S' produces a symbol from m (a string).
getcwd=:1!:43 NB. same as 'jcwdpath' but easier for me to remember.
chdir =:1!:44 NB.
