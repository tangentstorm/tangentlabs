{ 09/01/2013

  Program to demonstrate that using 'array of variant' in fpc
  will cause a runtime error 216 (general protection fault)
  unless a variant is explicitly declared or the 'variants'
  module is included.

  This code is in the public domain.
}
{$mode objfpc}
program variantbug;
{$IFDEF T0}
  uses variants;
{$ENDIF}

  procedure uncalled;
    {$IFDEF T1}
    var unused : variant;
    {$ENDIF}
  begin
  end;

procedure f( args : array of variant );
  {$IFDEF T2}
    var unused : variant;
  {$ENDIF}
  begin
  end;

{$IFDEF T3}
  var unused3 : variant;
{$ENDIF}
begin
  f([ 0 ]);
end.

{ output ( on freebsd / x64 )
-----------------------------------------------------
$ fpc -iW # although I get the same issue on 2.6.2
2.7.1

$ fpc -gl variantbug.pas && ./variantbug
Runtime error 216 at $0000000000423C3D
  $0000000000423C3D line 55 of x86_64/sighnd.inc

$ # but include any of the ifdef'd lines and it'll work fine:
$ fpc -dT0 -gl variantbug.pas && ./variantbug
$ fpc -dT1 -gl variantbug.pas && ./variantbug
$ fpc -dT2 -gl variantbug.pas && ./variantbug
$ fpc -dT3 -gl variantbug.pas && ./variantbug
}
