#!/usr/bin/env perl6
for lines() {
    say .subst( /\w/, 'x', :g );
}
