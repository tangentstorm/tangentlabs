#!/usr/bin/env perl6
=head1 Java -> Pascal Translator.
 Relies on on ANTLR4 to do the actual parsing.
=cut

use Term::ANSIColor;

grammar GRunTree {
    token TOP { <sexpr> }
    token sexpr {
	<lparen>
	$<head>=<grule> <ws>
	$<tail>=[ <atom> | <sexpr> | <symbol> | <ws> ]+?
        <rparen>
    }
    token ws     { $<tok>=[ '<EOF>' | \s+ ] }
    token grule   { $<tok>=\w+ }
    token atom   { $<tok>=\w+ }
    token lparen { $<tok>='(' }
    token rparen { $<tok>=')' }
    token symbol { $<tok>=\S }
}

class Actions {
    method ws($/) { print ~$<tok> }
    method lparen($/) { print colored ~$<tok>, "green"; }
    method rparen($/) { print colored ~$<tok>, "green"; }
    method grule($/)  { print colored ~$<tok>, "cyan"  }
    method atom($/)   { print BOLD() ~ colored( ~$<tok>, "white") ~ RESET() }
    method other($/)  { print colored ~$<tok>, "red" }
    method symbol($/) { print colored ~$<tok>, "red" }
}

chdir "%*ENV{'HOME'}/l/antlr";
my $antlr = "java org.antlr.v4.runtime.misc.TestRig";
my $grun  = "{$antlr} Java7 compilationUnit -tree";
my $file  = "~/ver/GameSketchLib/source/java/org/gamesketchlib/GsState.java";
my $cmd   = $grun ~ " " ~ $file;
my $gtree = qqx| $cmd |;

GRunTree.parse( $gtree, :actions( Actions ));
print "\n"
