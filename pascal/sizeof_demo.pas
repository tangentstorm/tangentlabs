{$mode objfpc}
program sizeof_demo;
type
  t	   = array[1..10] of byte;
  tclassx  = class
    x : t
  end;
  tclassy  = class
    x, y : t
  end;
  tobjectx = object
    x : t;
  end;
  tobjecty = object
    x, y : t
  end;
  pobjectx = ^tobjectx;
  pobjecty = ^tobjectx;

begin
  writeln;
  writeln( 'size of t:            ', sizeof( t )            : 3 );
  writeln( 'size of tclassx:      ', sizeof( tclassx )      : 3 );
  writeln( 'size of tclassy:      ', sizeof( tclassy )      : 3 );
  writeln( 'tclassx.instancesize: ', tclassx.instancesize   : 3 );
  writeln( 'tclassy.instancesize: ', tclassy.instancesize   : 3 );
  writeln( 'size of tobjectx:     ', sizeof( tobjectx )     : 3 );
  writeln( 'size of tobjecty:     ', sizeof( tobjecty )     : 3 );
  writeln( 'size of pobjectx:     ', sizeof( pobjectx )     : 3 );
  writeln( 'size of pobjecty:     ', sizeof( pobjecty )     : 3 );
  writeln;
end.
{
  output (note that i'm running on a 64-bit machine)
  Free Pascal Compiler version 2.6.2 [2013/03/17] for x86_64
  ...
  size of t:             10
  size of tclassx:        8
  size of tclassy:        8
  tclassx.instancesize:  24
  tclassy.instancesize:  32
  size of tobjectx:      10
  size of tobjecty:      20
  size of pobjectx:       8
  size of pobjecty:       8
}
