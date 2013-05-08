{$mode objfpc}
program sizeof_demo;
type
  tclassx = class x : integer; end;
  tclassy = class x, y : integer; end;
  tclassz = class x, y, z : integer; end;
  tobjectx = object x : integer; end;
  tobjecty = object x, y : integer; end;
  tobjectz = object x, y, z : integer; end;
begin
  writeln( 'size of classx:', sizeof( tclassx ));
  writeln( 'size of classy:', sizeof( tclassy ));
  writeln( 'size of classz:', sizeof( tclassz ));
  writeln( 'size of objectx:', sizeof( tobjectx ));
  writeln( 'size of objecty:', sizeof( tobjecty ));
  writeln( 'size of objectz:', sizeof( tobjectz ));
end.
{
  output (note that i'm running on a 64-bit machine)
  Free Pascal Compiler version 2.6.2 [2013/03/17] for x86_64
  ...
  size of classx:8
  size of classy:8
  size of classz:8
  size of objectx:4
  size of objecty:8
  size of objectz:12
}
