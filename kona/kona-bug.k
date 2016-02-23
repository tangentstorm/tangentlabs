/ script to expose an apparent bug in kona when combining 
/ higher-order verbs.

/ j-style "monadic fork": our first higher order verb.
mf: {[f;g;h] { g[f[x]; h[x]] }}

/ cheq = check equality of two strings. (or complain if mismatched)
cheq: { :[ x~y;  echo "."; echo "\nfailed: (", x, ") ~ (", y, ")\n"] }


/ symbolic functions (these return strings that show how they were called)
f: {"f[", x, "]" }
g: {"g[", x, "; ", y, "]"}
h: {"h[", x, "]" }

echo "testing first order verbs:\n"

test: {
  a: "a";  b: "b";
  cheq [ f[a];  "f[a]" ];
  cheq [ h[a];  "h[a]" ];
  cheq [ g[a; b];  "g[a; b]" ];
  cheq [ f[a];  "f[a]" ];
  cheq [ g[f[a]; h[a]]; "g[f[a]; h[a]]" ]


  / this is the test that fails. The ,/$: is to correct
  / for the mis-shapen results that are actually returned
  cheq [ ,/$: mf[f;g;h][a];  g[f[a]; h[a]]  ]
  echo "\n"
}
test()


echo "testing higher order verbs:\n"

/ higher order symbolic verbs
/ (these verbs take a string and construct a new verb)
sym1: {[s] {s, "[", x, "]" }}
sym2: {[s] {s, "[", x, "; ", y, "]"}}

f: sym1"f"
g: sym2"g"
h: sym1"h"

test()

echo "actual result, without formatting:\n"
echo mf[f;g;h]["a"]


/ output:
/ --------------------------------------
/ testing first order verbs:
/ ......
/ testing higher order verbs:
/ .....
/ failed: ([[a]; [a]]) ~ (g[f[a]; h[a]])
/ 
/ actual result, without formatting:
/ 
/ [
/ 
/ [
/ a
/ ]
/ ;
/ 
/ 
/ [
/ a
/ ]
/ ]
/ --------------------------------------
/
/ this indicates that the verbs returned by sym1 and sym2
/ function correctly when called explicitly, but somehow
/ lose track of their closed variables when passed to a
/ higher order verb like mf.
