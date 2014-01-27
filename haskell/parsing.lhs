
A parser attempts to transform a stream of input symbols (which
we will call 'characters', regardless of their type) into an
annotated tree of output symbols, or 'tokens'. Because this tree
is constructed according to the syntax rules of a particular
language, we call it a syntax tree.

If the parser is unable to produce a valid syntax tree from the input,
then it should produce an error instead.

> type Parser ch err syn = [ch] -> Either err syn

