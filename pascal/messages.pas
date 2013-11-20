// experiments with message methods
{$mode objfpc}
program messages;
uses variants;
const
  opSHO	= 0;
  opLIT	= 1;
  opADD	= 2;
  opGET	= 3;
type
  TMsgID   = cardinal;
  TMessage = packed record
	       code : TMsgId;
	       data : integer;
	     end;
type
  TDispatch = class
    _stack : array of Int32;
    constructor Create;
    procedure sho(var _ );             message opSHO;
    procedure lit(var a : TMessage);   message opLIT;
    procedure add(var _ );             message opADD;
    procedure get(var res : TMessage); message opGET;
  end;

constructor TDispatch.Create;
  begin
    SetLength(_stack, 0);
  end;

procedure TDispatch.sho(var _);
  var i : cardinal;
  begin
    write('[');
    if length(_stack) >= 1 then write(_stack[0]);
    if length(_stack) >  1 then
      for i := 1 to length(_stack) - 1 do write(', ', _stack[i]);
    writeln(']');
  end;
  
procedure TDispatch.lit(var a : TMessage);
  var i : cardinal;
  begin
    writeln('--> LIT ', a.data);
    i := Length(_stack);
    SetLength(_stack, i+1);
    _stack[i] := a.data;
  end;

procedure TDispatch.add(var _ );
  var i: cardinal;
  begin
    writeln('--> ADD ');
    i := Length(_stack);
    _stack[i-2] += _stack[i-1];
    SetLength(_stack, i-1);
  end;
  
procedure TDispatch.get(var res : TMessage);
  var i : cardinal;
  begin
    writeln('--> GET');
    i := Length(_stack);
    res.data := _stack[i-1];
    SetLength(_stack, i-1);
  end;

function Send(obj : TObject; code : TMsgID; data:Int32): Int32; overload; inline;
  var msg : TMessage;
  begin
    msg.code := code;
    msg.data := data;
    obj.dispatch(msg);
    result := msg.data;
  end;

function Send(obj : TObject; code : TMsgID): Int32; overload; inline;
  begin
    result := Send(obj, code, 0);
  end;

var x : TDispatch; i : integer;
begin
  writeln;
  x := TDispatch.Create;
  send(x, opSHO);
  send(x, opLIT, 2);
  send(x, opSHO);
  send(x, opLIT, 3);
  send(x, opSHO);
  send(x, opADD);
  send(x, opSHO);
  i := send(x, opGET);
  send(x, opSHO);
  writeln;
  writeln('Result: ', i);
  writeln;
  x.Free;
end.

{ output
------------

[]
--> LIT 2
[2]
--> LIT 3
[2, 3]
--> ADD
[5]
--> GET
[]

Result: 5

------------}
