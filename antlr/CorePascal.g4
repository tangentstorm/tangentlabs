grammar CorePascal;
parse : module ;

//--- parser -------------------------------------

module
    : modHeader
      block '.'
    ;

modHeader
    : 'module' IDEN ';'?
    ;

block
    : 'begin' ( statement ';' )* 'end'
    ;

statement
    : // pass
    ;

//--- scanner ------------------------------------

WHITESPACE
    : ('\u0000' .. '\u0020' )+  // space + all ascii control chars
        -> channel(HIDDEN)
    ;

IDEN
    : Alpha ( Alpha | Digit | '_' )*
    ;

fragment Alpha : 'a'..'z' | 'A'..'Z' ;
fragment Digit : '0'..'9' ;




/*

modHeader
    : 'module' iden ';'?
      'import' import (',' import)* ';'?
    ;





declaration
    : types
    | consts
    | vars
    | proc
    ;

types
    : 'type' (typedef ';')+
    ;

typedef
    : ( 'generic' iden ( '<' (iden ',')+ '>' )
      | iden
      )
      '='
      ( 
      | simpletype
      | classdef
      | recordef
      | setdef
      | rangedef
      )
    ;

*/
