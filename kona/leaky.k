

leaky:{[b] / b is a char picture of spaces (which conduct downward and left/right)
           / and other characters (which block the flow)
           / returns boolean indicating whether fluid can leak out the bottom.
  g: ,/ { _[;x] 0,&0,~=':x}' b=" "        / group alternating strings of 0s and 1s
  n: #[^b;]@ ,/g * +\*:' g                / 2d map with numbered horizontal groups
  e: + {x@ &~ 0 _in/: x}@ |:' ? ,/,'': n  / edges of digraph of flow between groups
  pos: {x@&x>0}                           / positive values only
  flow: {(e[1],0) @ e[0]?/: x}            / flow 1 step starting with groups in x
  a:  pos[?n 0]                           / starting nodes
  z:  pos[?,/ flow\ a]                    / list of all reached nodes
  r: |/ pos[?n[-1+#n]] _lin z             / final answer: any groups from the last row in z?
  :r}


\
/ example:

b:("##        #### ##"
    "#   #  #####    #"
    "   ##### ########"
    "   ##  #   #   ##"
    "##     ### # # ##"
    "###### ##### # ##"
    "##           # ##"
    "## ########### ##")

leaky b
