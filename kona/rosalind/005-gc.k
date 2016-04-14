/ http://rosalind.info/problems/gc/  (find string with highest percentage of G/C characters)

keys:(); vals:()                               / table as two parallel arrays

i:-1; s:""; lines: 0:"data.txt"                / parse the data.
while[(i:i+1) < #lines; ln: lines[i];          / for each line..
   if[ ln[0]=">"; keys:keys,,1_ ln;            /    if line starts with ">", store new key
       if[0<#s;   vals:vals,,s; s:""]];        /       and store built string (minus initial blank)
   if[~ln[0]=">"; s:s,ln]]                     /    else build string by appending this line.
vals: vals,,s

gcs: {n:+/|/"GC"=\: x; n % # x; n%%%#x}'vals   / GC score for each value
max: {x?|/x} gcs                               / position of the max value
`0: keys[max], "\n"                            / print corresponding key
`0: ($ 100*|/gcs), "\n"                        / print actual max score
