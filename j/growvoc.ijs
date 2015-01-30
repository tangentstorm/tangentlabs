NB. problem: given a database of words, find the longest chain of
NB. words such that each step in the chain differs by adding a single
NB. character to either the start or the end.
NB. http://codegolf.stackexchange.com/questions/45168

NB. approach: use a hash table to map each word to a number.
NB. also map its suffix (beheading) and prefix (curtailment).
's p'=:(*(>./i)>:])|:(6 s:[:s:}.;}:)S:0 w[i=:6 s:v=:s:w=:~.a:,<;._2 fread'voc'
l=:[:,([:(#S:0)5 s:_6 s:])"0 NB. verb mapping id to length
q=:_6 s: ] NB. return symbol for given id.

NB. follow links in a tree to find depth of each node.
f=:3 :'(y{~])^:(~:0:)^:a:"0 y' NB. follow nodes, making a chain.
d=:[: +/@:*"1 f NB. depth of node (length of chain)

NB. now choose either the prefix or suffix based on the longer chain.
n=:(ds<:dp)}s,:p[m=:ds>.dp NB. n=next link and m=max depth (of s or p)

NB. collect the chain, dropping the last item (0=empty string)
echo }:"1 q(r{i),.(r=:([:I.]=>./)m){f n
