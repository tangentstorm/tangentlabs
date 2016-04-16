/ kona (k3) port of trains from J
/ (limited to trains of 2 or 3 verbs only for now)

/ monadic and dyadic forks
mf: {[f;g;h] { g[f[x]; h[x]] }}
df: {[f;g;h] { g[f[x;y]; h[x;y]] }} 

/ monadic, and left/right dyadic identities:
id:{x}; lid:{y;x}; rid:{y}

/ hooks
mh: {[g;h] mf[ id; g; h]}
dh: {[g;h] df[lid; g; h]}

/ standard monadic fork example: avg (mean) = sum/count 
avg: mf[+/; %; #:]


/ -- test framework ---------------

/ ansi terminal stuff
color: {"\033[",($x),"m"}
reset: color 0
echo: {`0:$x}
endl: {echo reset,"\n"}
bold: color 1
red: color 31
grn: color 32 


/ symbolic functions (brute force)
x: "x";  y: "y";
f1: {"f1[", x, "]" }
g1: {"g1[", x, "]" }
h1: {"h1[", x, "]" }
f2: {"f2[", x, "; ", y, "]"}
g2: {"g2[", x, "; ", y, "]"}
h2: {"h2[", x, "; ", y, "]"}


/ higher order symbolic functions (better-in-theory...)
sym1: {[s] {s, "[", x, "]" }}
sym2: {[s] {s, "[", x, "; ", y, "]"}}

/ ... but for reasons I don't yet understand, these crash kona :/
/f1: sym1"f1";  g1: sym1"g1";  h1:sym1"h1"
/f2: sym2"f2";  g2: sym2"g2";  h2:sym2"h2"


/ check assertions, check equality
chek: {:[1~. x; echo grn,"."; echo red,$x,reset,"\n"]}
cheq: {chek "(", ($:x), ")~(", ($:y), ")"}
chex: { cheq[x; . x] }  / check expr evals to itself

/ these symbolic strings should evaluate to themselves:
chex "f1[x]"
chex "f2[x; y]"
chex "f1[f1[x]]" 
chex "g2[f1[x]; h1[x]]"

/ now here's how forks and hooks work:
cheq [ df[f2; g2; h2][x; y];   g2[f2[x; y]; h2[x; y]] ]
cheq [ mf[f1; g2; h1][x];      g2[f1[x];    h1[x]] ]

cheq [ dh[g2; h2][x; y];       g2[x; h2[x; y]] ]
cheq [ mh[g2; h1][x];          g2[x; h1[x]] ]

endl()
