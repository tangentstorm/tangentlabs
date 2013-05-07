{ 5/6/2013

  Q : can you use the 'array of const' syntax outside of a procedure?
  A : no, but you can use 'array of variant' along with a function.
}
{$mode objfpc}
program arrayofconst;
uses variants;

type
  TVars =  array of variant;
  // TConsts = array of const; { Error: Illegal expression }

procedure printall_c( consts : array of const );
  var i : integer;
  begin
    for i := low(consts) to high(consts) do
      with consts[i] do
	case vtype of
	  vtInteger    : writeln( vinteger );
	  vtAnsiString : writeln( ansistring( vstring ));
	  vtextended   : writeln( vextended^ );
	end;
  end;

procedure printall_v( vars : array of variant );
  var v : variant;
  begin
    for v in vars do writeln( v );
  end;


function variants( aov : array of variant ) : TVars;
  var i : integer;
  begin
    // result := aov; { Incompatible types: got "{Open} Array Of Variant" expected "TVars" }
    setlength(result, length(aov));
    for i := low(aov) to high(aov) do
      result[ i ] := aov[ i ];
  end;

const
  three	= 3;
var
  four	 : integer = 4;
  vars	 : TVars;
  // var c : array of const; { Error: Illegal expression }

begin

  writeln('---| array of const:');
  printall_c([ 0, 1.0, 1.1, 'two', three, four ]);

  writeln('---| array of variant:');
  printall_v([ 0, 1.0, 1.1, 'two', three, four ]);

  // vars := [ 0, 1.0, 1.1, 'two', three, four ]; { Error: Ordinal expression expected }
  vars := variants([ 0, 1.0, 1.1, 'two', three, four ]);

  writeln('---| variant array: ');
  // printall_c( vars ); { Incompatible type for arg no. 1: Got "TVars", expected "Array Of Const" }
  printall_v( vars );
  
end.

{
  OUTPUT (only difference apears to be the format of the extended number)

  $ fpc arrayofconst.pas && ./arrayofconst
  Free Pascal Compiler version 2.6.2 [2013/03/17] for x86_64
  Copyright (c) 1993-2012 by Florian Klaempfl and others
  Target OS: Linux for x86-64
  Compiling arrayofconst.pas
  Linking arrayofconst
  /usr/bin/ld: warning: link.res contains output sections; did you forget -T?
  70 lines compiled, 0.1 sec
  ---| array of const:
  0
  1.0000000000000000E+0000
  1.1000000000000000E+0000
  two
  3
  4
  ---| array of variant:
  0
  1
  1.1
  two
  3
  4
  ---| variant array:
  0
  1
  1.1
  two
  3
  4
}
