// prototype for calling j from pascal
{$mode objfpc}
program callj;
uses xpc,dynlibs;

type
  JS = PAnsiChar;
  JI = Int32;
  JA = pointer;
  JJ = pointer;
  TJCBs  = array [0..4] of pointer; // callbacks
  TJInit = function : JS; stdcall;
  TJSM   = procedure(j:JJ; var cb:TJCBs); stdcall;
  TJDo   = function(j:JJ; s:JS):JI; stdcall;
  TJFree = function(j:JJ):JI; stdcall;
  TJGetL = function(j:JJ):JS; stdcall;
  TJGetA = function(j:JJ; n:JI; name:JS):JA; stdcall;
  TJSetA = function(j:JJ; n:JI; name:JS; x:JI; data:JS):JI; stdcall;

var
  JInit	: TJInit;
  JDo	: TJDo;
  JSM	: TJSM;
  JFree	: TJFree;
  JGetL : TJGetL;
  JGetA : TJGetA;
  JSetA : TJSetA;

procedure DoWr(j:JJ;len:JI;s:JS); stdcall;
  begin write(s)
  end;

function DoRd(j:JJ; s:JS):JS; stdcall;
  var r:RawByteString;
  begin write(s); readln(r); result:=JS(r);
  end;

var jlib: TLibHandle; j:JJ; s:RawByteString='';
    jcb:TJCBs=(@DoWr, Nil, @DoRd, Nil, Pointer(3));
begin
  jlib := LoadLibrary('./libj.so');
  if jlib = NilHandle then writeln('failed to load jlib')
  else writeln('j loaded');

  JInit := TJInit(GetProcedureAddress(jlib, 'JInit'));
  JSM   := TJSM(GetProcedureAddress(jlib, 'JSM'));
  JDo   := TJDo(GetProcedureAddress(jlib, 'JDo'));
  JFree := TJFree(GetProcedureAddress(jlib, 'JFree'));
  JGetL := TJGetL(GetProcedureAddress(jlib, 'JGetLocale'));
  JGetA := TJGetA(GetProcedureAddress(jlib, 'JGetA'));
  JSetA := TJSetA(GetProcedureAddress(jlib, 'JSetA'));

  j := JInit(); // careful! need () because it's a variable!
  JSM(j, jcb);
  repeat
    if s<>'' then JDo(j, JS(s)) else ok;
    write('   '); readln(s);
  until s='bye';
  JFree(j);
end.
