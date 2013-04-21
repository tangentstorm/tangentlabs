#!/usr/bin/env perl6
=head1 AntlrTree
Tree builder that uses output from ANTLR4
=cut

use Term::ANSIColor;

grammar GRunTree {
  token TOP { <sexpr> }
  token sexpr {
     <new_node>
        <head> <space> [ <body> | <sexpr> | <punct> | <space> ]+?
     <end_node>
  }
  token new_node { '(' }
  token head { $<tok>=\w+ }
  token body { $<tok>=\w+ }
  token punct { $<tok>=\S }
  token space { $<tok>=[ '<EOF>' | \s+ ] }
  token end_node { ')' }
}

class Node {
  has $.head is rw;
  has @.body;
  submethod BUILD { $!head = ""; @!body = [] }
  method append( $item ) { @!body.push( $item ) }
}

class TreeBuilder {
  has $.root;
  has $!node;
  has @!path;

  submethod BUILD {
    $!root = Node.new;
    $!root.head = '<root>';
    $!node = $!root;
    @!path = [];
  }

  method new_node($/) { @!path.push( $!node ); $!node = Node.new }
  method end_node($/) { 
    my $temp = $!node;
    $!node = @!path.pop;
    $!node.append( $temp );
  }
  method head($/) { $!node.head = ~$<tok> }
  method body($/) { $!node.append( ~$<tok> ) }
  method punct($/) { $!node.append( ~$<tok> ) }
  method space($/) { $!node.append( ~$<tok> ) }
}

sub descend( $node ) {
  (.isa( Node ) ?? transform( $_  ) !! $_ for $node.body
  ).join( '' )
}

sub transform( $node ) {
  given $node.head {
    default { descend($node) }
  }
}


chdir "%*ENV{'HOME'}/l/antlr";
my $antlr = "java org.antlr.v4.runtime.misc.TestRig";
my $grun  = "{$antlr} Java7 compilationUnit -tree";
my $file  = "~/ver/GameSketchLib/source/java/org/gamesketchlib/GsState.java";

my $builder = TreeBuilder.new;
GRunTree.parse( qqx| $grun $file |, :actions( $builder ));
my $tree = $builder.root;

say transform($tree);
