#lang brag
b-program : [b-line] (/NL [b-line])*
b-line : b-line-num [b-statement] (/":" b-statement)* [b-rem]
@b-line-num : INTEGER
@b-statement : b-end | b-print | b-goto
b-rem : REM
b-end : /"end"
b-print : /"print" [b-printable] (/";" [b-printable])*
@b-printable : STRING | b-expr
b-goto : /"goto" b-expr
b-expr: b-sum
b-sum : b-number (/"+" b-number)*
@b-number : INTEGER | DECIMAL
