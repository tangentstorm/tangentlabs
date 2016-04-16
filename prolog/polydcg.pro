% polydcg : a small dcg to combine simple polynomials
:- use_module(library(dcg/basics)).

% grammar for polynomials

poly --> term.
term --> factor, ("+"; "-"), factor.
term --> factor.
factor --> exponent
	 ; (constant, ("*";[]), exponent) % 
	 ; constant
	 .
exponent --> ("x", "^", constant) ; "x" .
constant --> digit, (constant;[]).
digit --> "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9".

% example:
% (poly,"x+2x^3").
