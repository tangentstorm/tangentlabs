//
// Q: Is it possible to assign a function to a variant so that
//    variants can be called directly? (And thus used for higher
//    order functions?)
//
// A: No. It won't get past the parser (as of sep 2013).
//    However, you *can* call methods on a variant.
//
{$mode objfpc}
procedure varcall;
var f : variant;
begin
  f.call(0,0);  // parses fine
  f(0,0);       // syntax error: ";" expected but "(" found
end.

{ $ fpc -l varcall.pas
  Free Pascal Compiler version 2.7.1 [2013/09/01] for x86_64
  Copyright (c) 1993-2013 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling varcall.pas
  varcall.pas(9,3) Warning: Local variable "f" does not seem to be initialized
  varcall.pas(10,4) Error: Illegal expression
  varcall.pas(10,4) Fatal: Syntax error, ";" expected but "(" found
  Fatal: Compilation aborted }
