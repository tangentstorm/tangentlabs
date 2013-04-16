// see:
// $ make hello

// Define a grammar called Hello
// match keyword hello followed by an identifier
// match lower-case identifiers
grammar Hello;
r : 'hello' ID ;
ID : [a-z]+ ;
WS : [ \t\n]+ -> skip ; // skip spaces, tabs, newlines
