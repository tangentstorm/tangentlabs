/ http://rosalind.info/problems/subs/  (find substrings)
find: {& y~/: (#y) #' (!#x) !\: x}   / find substring like _ss, but allow overlaps.
1 + find/(0:"data.txt")              / find second line of input inside first line (1-based indices)
