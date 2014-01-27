
A parser attempts to transform a stream of input symbols (which
we will call 'characters', regardless of their type) into an
annotated tree of output symbols (or 'tokens'), called
a syntax tree.

If the parser is unable to perform this transformation, then it
produces an error message instead.

> type Parser ch err syn = [ch] -> Either err syn

