{ Q: is there a runtime cost to casting a pointer?
  (in response to a question in #fpc Fri Sep 6 2013)
  
  My guess is that the two are equivalent because the
  pointer's type is only there to appease the compiler,
  and there's nothing about types tracked at runtime
  by default.

  A: there is no cost. the generated assembly files
  were identical once debug information was disabled
  in the compiler configuration.
}
program castptr;
var
  d : dword;
  {$IFDEF DOCAST}
  p : pointer;
  {$ELSE}
  p : pdword;
  {$ENDIF}
begin
  d := 9999;
  p := @d;
  {$IFDEF DOCAST}
  pdword(p)^ := 1234;
  {$ELSE}
  p^ := 1234;
  {$ENDIF}
  writeln(d);
end.
{
I tested with:
  
fpc -a -dNOCAST castptr.pas -oNOCAST
mv castptr.s nocast.s
fpc -a -dDOCAST castptr.pas -oDOCAST
mv castptr.s docast.s
diff nocast.s docast.s


The -a switch causes fpc to leave a copy of the
generated assembly language code.
  
There were a few lines of difference initially,
but they were only because I had the -gl switch
(to include debug information) enabled in my fpc.cfg
file. Once I removed this, the generated files
were identical.
}
