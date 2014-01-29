> module Main where
> import Test.HUnit
> import Data.List

A parser attempts to transform a stream of input symbols (which
we will call 'characters', regardless of their type) into an
annotated tree of output symbols, or 'tokens'. Because this tree
is constructed according to the syntax rules of a particular
language, we call it a syntax tree.

If the parser is unable to produce a valid syntax tree from the input,
then it should produce an error instead.

> type Parser ch err syn = [ch] -> Either err syn

== Grammar Combinators ==

- Parsers are easy but tedious
  - tend to be rather large and complicated
  - lots of code that's /almost/ the same, but not quite.

- Possible Approaches:
  - make languages simpler (lisp, forth, smalltalk, apl, xml, oberon)
  - generate parser from description of the grammar (yacc, antlr gold)
  - compose smaller parsers with parser combinator libraries (parsec, ...)

- Our approach:
  - compose grammars, not parsers
  - grammar combinators produce transparent data structures
  - this gives us options:
    - interpret grammar description directly
    - compose parser functions on the fly
    - inspect and simplify grammar rules
    - generate parsers for other languages (do what antlr does)
    - generate grammars for other tools (let antlr do it for us)

- Sequential Composition (pipelines)
  - lexer -> parser -> tree transform -> codegen / pretty printing
  - algebraic data types at every step
  - ... all the way down to machine code if we want

- Let's work with a specific and (somewhat) simple language (J)
  - ascii characters
  - but: grammar is context sensitive

We will begin with the end in mind, and describe the syntax trees we want
our parser to produce.

== High level structure for J syntax trees ==

> data Id = Id [Char]
> data Jx s
>   = Noun           s          -- sequence of numbers, separated by spaces
>   | Prim           s          -- j primitive
>   | Quote          s          -- array of characters
>   | Gerund         s          -- array of verbs
>   | Pronoun Id     s          -- an identifier
>   | MoVerb         s (Jx s)   -- verb with one argument (on its right)
>   | DyVerb  (Jx s) s (Jx s)   -- verb with two arguments (one on either side)
>   | Adverb  (Jx s) s          -- modifies a verb (to its left)
>   | Copula   Id    s (Jx s)   -- assignment / definition
>   | Conj    (Jx s) s (Jx s)   -- conjunction
>   | Hook    [Jx s] s          -- train with an even number of verbs
>   | Fork    [Jx s] s          -- train with an odd number of verbs


== Simple examples. ==

J is relatively easy to tokenize.

> sDOT    = Sym ':'
> sCOLON  = Sym ':'
> sSPACE  = Sym ' '
> sQUOTE  = Sym '\''
> sALPHA  = Any $ ['a'..'z']++['A'..'Z']
> sDIGIT  = Any $ ['0'..'9']
> sUNDER  = Sym '_'
> sNEWLN  = Sym '\n'

> jNB   = Lit "NB."
> jstr  = Seq [ sQUOTE, Orp [ Not [ sQUOTE, sNEWLN ] ],  sQUOTE ]
> jprim = Alt


> data Gram c
>    = Nul
>    | Sym c
>    | Any [c]       -- Lit s <--> Alt $ map Sym s
>    | Lit [c]       -- Lit s <--> Seq $ map Sym s
>    | Not [Gram c]
>    | Alt [Gram c]
>    | Seq [Gram c]
>    | Rep [Gram c]
>    | Opt [Gram c]  -- Opt g <--> Alt [ Nil, g ]
>    | Orp [Gram c]  -- Orp g <--> Opt Rep g
>      deriving (Show, Eq)

== scraps ==

> type Lexer ch = Parser ch () [ch]
> type ChLex = Lexer Char

For example, if `p`, and `q` are parsers that each
match a small pattern, then they might be combined together by
introducing a combinator called `andthen`:

> andthen :: ChLex -> ChLex -> ChLex
> andthen p q = \cs -> p cs >>= q
