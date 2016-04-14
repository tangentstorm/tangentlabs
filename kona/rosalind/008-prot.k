/ http://rosalind.info/problems/prot/    (rna → protein)

tbl:"
UUU F      CUU L      AUU I      GUU V
UUC F      CUC L      AUC I      GUC V
UUA L      CUA L      AUA I      GUA V
UUG L      CUG L      AUG M      GUG V
UCU S      CCU P      ACU T      GCU A
UCC S      CCC P      ACC T      GCC A
UCA S      CCA P      ACA T      GCA A
UCG S      CCG P      ACG T      GCG A
UAU Y      CAU H      AAU N      GAU D
UAC Y      CAC H      AAC N      GAC D
UAA _      CAA Q      AAA K      GAA E
UAG _      CAG Q      AAG K      GAG E
UGU C      CGU R      AGU S      GGU G
UGC C      CGC R      AGC S      GGC G
UGA _      CGA R      AGA R      GGA G
UGG W      CGG R      AGG R      GGG G"

cols: {[x;y](((#y)%x),x) # y}   / reshape y as x columns

/ parse above into a 2-column table:
tbl: _ssr[tbl;"\n";" "]         / newlines → spaces
tbl: {x@&a|1_1!1,a:~x=" "} tbl  / condense spaces 
tbl: {1_'(&x=" ") _ x} tbl      / split on whitespace
tbl: `$'tbl                     / strings to symbols
tbl: +cols[2;tbl]               / reshape as 2 columns
r2p[tbl@0]:tbl@1;               / rna sequence → protein dictionary
pro: {-1_,/$r2p[`$'cols[3;x]]}  / rna string → protien string converter.

`0:pro[,/0:"data.txt"],"\n"     / convert and print the given rna string.
