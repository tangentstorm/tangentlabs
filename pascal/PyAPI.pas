{$mode delphi}
unit PyAPI;

{
   Minimum set of Python function declarations for module libraries.

   Author: Phil (MacPgmr at fastermac.net).

   To add other Python function declarations, see the Python header
   files (.h) included with every Python distribution.
}

interface

const
  {$IFDEF MSWINDOWS}
  PythonLib = 'python27.dll';
  {$ELSE}
  PythonLib = 'libpython2.7.so';
  {$ENDIF}

type
  PyMethodDef = packed record
    Name: PChar;     // Python function name
    meth: Pointer;   // Address of function that implements it
    flags: integer;  // METH_xxx flags; describe function's arguments
    doc: PChar;      //Description of funtion
  end;

  PyObject = Pointer;

const
  PYTHON_API_VERSION = 1013;     // Include/modsupport.h:46
  METH_VARARGS = 1;

function Py_InitModule(
	       Name    : PChar;
	   var methods : PyMethodDef;
	       doc     : PChar = nil; self: PyObject = nil;
	       apiver  : longint = PYTHON_API_VERSION
	       )       : PyObject;
  cdecl; external PythonLib Name 'Py_InitModule4_64';

function PyArg_ParseTuple(
	   args	  : PyObject;
	   format : PChar
	   )	  : integer;
  cdecl; varargs; external PythonLib;

function PyInt_FromLong(
	   along : longint
	   )	 : PyObject;
  cdecl; external PythonLib;


implementation


end.
