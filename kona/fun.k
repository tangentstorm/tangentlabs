/ fun/useful kona toys

/ eval an expression to test it. (assert, basically)
chek: {if[~. x; `0:"failed: ",x,"\n"]}

/ multiple assignment:
set:{.[x;();:;y]}'
set:.[;();:;]'        / magic simplification courtesy of geocar!

set[`a`b`c; 11 22 33]
chek["(a=11)&(b=22)&(c=33)"]
