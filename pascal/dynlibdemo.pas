// program to demonstrate opening a dynamic library
// and fetching the address of a symbol.

program dynlibdemo;
uses dynlibs, sysutils;

const symbol = 'Py_DebugFlag';

var lib : TLibHandle; p : pointer;
begin
  lib := LoadLibrary('libpython2.7.so');
  if lib = NilHandle then
    writeln('LoadLibrary error: ', GetLoadErrorStr)
  else begin
    p := GetProcAddress(lib, symbol);
    if p = nil then WriteLn('GetProcAddress error: ', GetLoadErrorStr)
    else WriteLn(Format('Symbol %s is at address %P', [symbol, p]));
  end;
  FreeLibrary(lib);
end.
{-- output -----------
 
   Symbol Py_DebugFlag is at address 0000000800F77CA0

 --------------------- }
