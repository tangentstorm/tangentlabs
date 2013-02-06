library HelloPy;
{$MODE OBJFPC}
{

  Minimal Python module (library) that includes a single function.

  Author: Phil (MacPgmr at fastermac.net).

  For a good explanation of modules from a C perspective, see:
    http://superjared.com/entry/anatomy-python-c-module/

  To compile this module:
    - With Delphi: Open this .dpr file and compile.
    - With Lazarus: Open .lpi file and compile.

  To deploy module:
    - With Delphi: Rename compiled .dll to .pyd.
    - With Lazarus on Windows: Rename compiled .so to .pyd.
    - With Lazarus on OS X and Linux: .so extension is okay.

}




uses
  SysUtils,
  PyAPI;


function SumTwoIntegers(Self : PyObject; Args : PyObject)
  : PyObject; cdecl;
var
  Arg1 : Integer;
  Arg2 : Integer;
begin
  PyArg_ParseTuple(Args, 'ii', @Arg1, @Arg2); // Get the two input arguments
  Result := PyInt_FromLong(Arg1 + Arg2);      // Add them and return the sum
end;


var
  Methods : packed array [0..1] of PyMethodDef;

procedure initHelloPy;
  cdecl;
begin
  Methods[0].name := 'SumTwoIntegers';
  Methods[0].meth := @SumTwoIntegers;
  Methods[0].flags := METH_VARARGS;
  Methods[0].doc := 'Tests argument passing to and from module function';

  Methods[1].name := nil;
  Methods[1].meth := nil;
  Methods[1].flags := 0;
  Methods[1].doc := nil;

  Py_InitModule('HelloPy', Methods[0]);
end;


exports
  initHelloPy;

end.
