#!/usr/bin/env perl6
=comment
Universal forth-style tokenizer (breaks on whitespace)
=cut

grammar Grammar {
    token TOP { [ <whitespace> | <blackspace> ]+ }
    token whitespace { \s+ }
    token blackspace { $<token>=[\S+] }
}

class Actions {
    method blackspace($/) { say ~$<token> }
}

my @tokens = Grammar.parse( slurp, :actions( Actions ));
