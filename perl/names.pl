#!/usr/bin/perl

# q: are sigils in perl part of the name?
# a: yes.

$a = "a string...";
@a = ( "and","a","list..." );
%a = ( 'and' => 'a hash!' );

print $a;
for ($x=0; $x<3; $x++) { print $a[$x], " "; }
for (keys %a) { print $_, " ", $a{$_}; }
print "\n";

__DATA__

output is:

$ perl names.pl
a string...and a list... and a hash!

