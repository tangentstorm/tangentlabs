#lang brag
bf-program : (bf-op | bf-loop)* ;
bf-op      : "<" | ">" | "," | "+" | "-" | "." | "," ;
bf-loop    : "[" (bf-op | bf-loop)* "]" ;