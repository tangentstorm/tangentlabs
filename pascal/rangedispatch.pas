{ Q: can you use range types together with function
     overloading to do dynamic dispatch based on a value?
  A: No. }
program rangedispatch;

type
  lo = $0..$7;
  hi = $8..$f;

procedure f(x : lo ); begin write('lo') end;
procedure f(x : hi ); begin write('hi') end;

var i : byte;
begin
  for i := 0 to $f do writeln(i, ' is ', f(i));
end.
{ compiler output:

  Free Pascal Compiler version 2.7.1 [2014/05/09] for x86_64
  Copyright (c) 1993-2014 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling rangedispatch.pas
  rangedispatch.pas(14,42) Error: Can't determine which overloaded function to call
  rangedispatch.pas(17,8) Fatal: There were 1 errors compiling module, stopping
  Fatal: Compilation aborted
}