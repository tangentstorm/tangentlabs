// prototype for calling j from pascal
// this program supports using cwio as a wrapper for
// multi-colored text output and keyboard i/o
{$mode delphiunicode}{$i xpc}
program callj;
uses xpc,dynlibs;

type
  JS     = PAnsiChar;
  JI     = Int32;
  JA     = ^TJA;
  JJ     = pointer;
  TJCBs  = array [0..4] of pointer; // callbacks
  TJInit = function : JS; stdcall;
  TJSM   = procedure(j:JJ; var cb:TJCBs); stdcall;
  TJDo   = function(j:JJ; s:JS):JI; stdcall;
  TJFree = function(j:JJ):JI; stdcall;
  TJGetL = function(j:JJ):JS; stdcall;
  TJGetA = function(j:JJ; n:JI; name:JS):JA; stdcall;
  TJSetA = function(j:JJ; n:JI; name:JS; x:JI; data:JS):JI; stdcall;
  TJA    = record
             k,flag,m,t,c,n,r,s : JI;
             v: array [0..0] of JI; // really it's dynamically sized
           end;

var
  JInit : TJInit;
  JDo   : TJDo;
  JSM   : TJSM;
  JFree : TJFree;
  JGetL : TJGetL;
  JGetA : TJGetA;
  JSetA : TJSetA;
  jwaiting:boolean=false; // is j awaiting input?

// write text to screen
procedure DoWr(j : JJ;len:JI;s:JS); stdcall;
  var i:byte;
  begin
    if (len > 0) and (s[0] in [^E, ^K]) then begin jwaiting:=true end;
    write(s); flush(output);
  end;

// read input from keyboard
function DoRd(j:JJ; s:JS):JS; stdcall;
  var r:RawByteString;
  begin
    if jwaiting then jwaiting := false // j code already told cwio to expect input
    else begin writeln(^E); flush(output); end;
    readln(r); result:=JS(r);
  end;

// window driver
function DoWd(j : JJ; x:JI; a:JA; var res:JA) : JI;
  var wdres:TStr;jres:AnsiString;
  begin
    { writeln('Wd: x=', x, '  k: ',a^.k, ' flag: ',a^.flag, ' m: ',a^.m,
      t: ',a^.t, ' c: ',a^.c, ' n: ',a^.n, ' r: ',a^.r ); }
    case x of
      0 : wdres:='i.5';
      1 : wdres:='i.10';
    otherwise
      wdres:='i.25';
    end;
    wdres:='wdres_z_=:'+wdres; jres:=u2a(wdres);
    JDo(j, @jres[1]); res := a; result:= 0;
  end;

var jlib: TLibHandle; j:JJ; s:RawByteString='0!:0<''callj.ijs''';
    jcb:TJCBs=(@DoWr, @DoWd, @DoRd, Nil, Pointer(3));
begin
  jlib := LoadLibrary('./libj.so');
  if jlib = NilHandle then writeln('failed to load jlib')
  else begin
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
      if s='' then ok else JDo(j, JS(s));
      writeln('   ',^E); flush(output); readln(s);
    until (s='bye') or ((length(s)=1) and (s[1]=^D));
    JFree(j);
  end;
end.
