require 'stype.ijs'
import each 'boxer';'dict';'unify'

NB. G holds the grammar
G=:emptyd

NB. defrule name (text) defines a new rule.
NB. format is: (node template) (patterns) (text template)
defrule=: 3 :'G =: (y S) put (< sx (0 : 0)) G'

NB. (rule 'name') fetches the rule from the system as a triple
rule =: 3 : ',> G get sym y'

NB. special formatting symbols:
'NL SP'=:sym'\n _'

NB. grammar for a PL0-like language

defrule 'program'
  ($name $imps     $decs  $body)
  (iden  imports?  decl*  block)
  ("program" _ $name ";" \n
    $imps
    $decs \n
    $body ".")
)

defrule 'imports'
  ($mods)
  (iden*)
  ("import" _ ";" \n)
)

defrule 'writeln'
  ($args)
  (expr*)
  ("WriteLn(" $args / ","  ")")
)

defrule 'str'
 ($s) ($s) ("\"" $s "\"")
)



head =: ,@>@{.@,
tail =: }.@,

NB. render leaves, colored according to datatype
render =: reset ,~ [: ; (3 : 0)
  select. stype y
  case. BOX do.
    if. 1=#y do. render >y
    else. NB. rule triple for node
      'n r t'=: ,>G get (head y)
      R=:((;n) dict tail y) subs t
    end.
  case. TXT do. (fg'W'),y
  case. NUM do. (fg'Y'),":y
  case. SYM do.
    select. y
    case. NL do. LF
    case. SP do. ' '
    case. do. (fg'c'), 2 s:y  NB. sym→str
    end.
  case. do. (fg'w'),":y
  end.
)

NB. an example program
p =: sx 0 : 0
  (program hello ( ) ( )
    (block (writeln (str "hello, world.")) ))
)
