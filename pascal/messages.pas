// experiments with message methods
{$mode objfpc}{$h+}
program messages;
uses variants;
const
  opSHO	= 0;
  opLIT	= 1;
  opADD	= 2;
  opGET	= 3;
  opMSG = 4;
type
  TMsgID   = cardinal;
  TMessage = packed record
	       code : TMsgId;
	       data : variant;
	     end;
type
  TDispatch = class
    _stack : array of Int32;
    constructor Create;
    procedure sho(var _ );             message opSHO;
    procedure lit(var a : TMessage);   message opLIT;
    procedure add(var _ );             message opADD;
    procedure get(var res : TMessage); message opGET;
    procedure msg(var msg : TMessage); message opMSG;
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

procedure TDispatch.msg(var msg : TMessage);
  begin
    writeln('--> MSG ', msg.data);
    msg.code := 123; // reuse code field to send another message back.
    msg.data := 'response';
  end;

function Send(obj : TObject; code: TMsgID; i:variant; out o: variant): TMsgID;
  overload; inline;
  var msg : TMessage;
  begin
    msg.code := code;
    msg.data :=	i;
    obj.dispatch(msg);
    result := msg.code;
    o := msg.data;
  end;
  
function Send(obj : TObject; code : TMsgID; data:variant): TMsgID;
  overload; inline;
  var tmp:variant;
  begin
    result := send(obj, code, data, tmp);
  end;

function Send(obj : TObject; code : TMsgID): variant;
  overload; inline;
  var tmp: variant;
  begin
    result := Send(obj, code, tmp);
  end;

var x : TDispatch; v, i : variant;
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
  send(x, opGET, null, v);
  send(x, opSHO);
  writeln;
  writeln('Result: ', v);
  writeln;
  i := send(x, opMSG, 'query', v);
  writeln('response code: ', i);
  writeln('response data: ', v);
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

--> MSG query
response code: 123
response data: response

------------}
