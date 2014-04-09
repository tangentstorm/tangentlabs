// experiments with message methods
{$mode objfpc} // from https://github.com/tangentstorm/xpl
program messages;
uses xpc, variants, stacks;
const
  opSHO	= 0; // show the stack
  opLIT = 1; // add literal value (from the TIntMsg) to the stack
  opADD = 2; // add top two items
  opPOP = 3; // return top item
  opAAA = 4; // just an arbitrary message

  // for these two, i wanted to see how to list the string messages
  // to see if it might be usable for dynamic dispatch.
  {$h-}
  msgABC = 'ABC';  msgXYZ = 'XYZ';
  {$h+}

// the messages can be in any format but for int messages,
// the first dword has to be the numeric code, and for strings,
// the first n bytes are a shortstring (the first byte is the length)
// i'm arbitrarily capping string messages to 16 chars.
type
  TIntMsgId = dword;
  TStrMsgId = string[16];
  TIntStack = specialize GStack<Int32>;
  TIntMsg   = packed record
		code : TIntMsgId;
		data : variant;
	      end;
  TStrMsg   = packed record
		code : TStrMsgId;
		data : variant;
	      end;

type
  TDispatch = class
    stack : TIntStack;
    constructor Create;
    destructor Destroy; override;
    procedure sho(var _ );            message opSHO; // message msgSHO; nope[0]
    procedure lit(var a : TIntMsg);   message opLIT;
    procedure add(var _ );            message opADD;
    procedure pop(var res : TIntMsg); message opPOP;
    procedure aaa(var msg : TIntMsg); message opAAA;
    procedure abc(var msg : TStrMsg); message msgABC;
    procedure xyz(var msg : TStrMsg); message msgXYZ;
    procedure DefaultHandlerStr( var message ); override;
  end;
// [0] only 1 message can be used per method, even if different types


{ TDispatch }

constructor TDispatch.Create;
  begin self.stack := TIntStack.Create(16);
  end;

destructor TDispatch.Destroy;
  begin self.stack.free
  end;

procedure TDispatch.sho(var _);
  var i : cardinal;
  begin
    write('[');
    if stack.count > 0 then begin
      write(stack[0]);
      if stack.count > 1 then
	for i := 1 to stack.count - 1 do write(', ', stack[i]);
    end;
    writeln(']');
  end;

{ TDispatch int messages }

procedure TDispatch.lit(var a : TIntMsg);
  begin stack.push(a.data); writeln('--> LIT ', a.data);
  end;

procedure TDispatch.add(var _ );
  begin stack.push(stack.pop + stack.pop); writeln('--> ADD ');
  end;

procedure TDispatch.POP(var res : TIntMsg);
  begin res.data := stack.pop; writeln('--> POP');
  end;

procedure TDispatch.aaa(var msg : TIntMsg);
  begin
    writeln('--> AAA', msg.data);
    msg.code := 123; // reuse code field to send another message back.
    msg.data := 'response';
  end;


{ TDispatch string messages }

procedure TDispatch.abc( var msg : TStrMsg );
  begin writeln( '--> ABC' ); msg.data := 'abc ok';
  end;

procedure TDispatch.xyz( var msg : TStrMsg );
  begin writeln( '--> XYZ' ); msg.data := 'xyz ok';
  end;

procedure TDispatch.DefaultHandlerStr( var message );
  begin
    writeln('--> unknown str message:' );
  end;


// different ways to send messages

// for when you need a response. (send null for param i if no arg)
function Send(obj : TObject; code: TIntMsgId; i:variant; out o: variant): TIntMsgId;
  overload; inline;
  var msg : TIntMsg;
  begin
    msg.code := code;
    msg.data :=	i;
    obj.dispatch(msg);
    result := msg.code;
    o := msg.data;
  end;

// for when you have a parameter but don't need a response
function Send(obj : TObject; code : TIntMsgId; data:variant): TIntMsgId;
  overload; inline;
  var tmp : variant;
  begin
    tmp := 0;
    result := send(obj, code, data, tmp);
  end;

// for when you're just sending a message
function Send(obj : TObject; code : TIntMsgId): variant;
  overload; inline;
  begin result := Send(obj, code, 0);
  end;

// for the string messages:

function SendStr(obj : TObject; s : string) : variant;
  var msg : TStrMsg;
  begin
    msg.code := s; msg.data := null;
    obj.dispatchStr(msg);
    result := msg.data;
  end;

const takesVal : set of byte = [ opLIT ];
const givesVal : set of byte = [ opPOP ];

// a little command interpreter
procedure script(x : TDispatch; code : array of variant; var result : variant);
  var c : dword; i : integer = 0;
  begin
    while i <= high(code) do begin
      c := code[i];
      if c in takesVal      then send(x, c, code[incv(i)])
      else if c in givesVal then send(x, c, null, result)
      else                       send(x, c);
      send(x, opSHO); inc(i);
    end
  end;

var x : TDispatch; v, i : variant;
begin
  writeln;
  x := TDispatch.Create;

  // 2 3 + -> 5
  script(x, [opLIT, 2, opLIT, 3, opADD, opPOP], v);
  assert(v = 5); writeln; writeln('Result: ', v);
  writeln;

  i := send(x, opAAA, 'query', v); // invoke TDispatch.msg
  writeln('response code: ', i);  assert( i = 123 );
  writeln('response data: ', v);  assert( v = 'response' );
  writeln;

  v := sendStr(x, msgABC); writeln('response:', v); assert( v = 'abc ok' );
  v := sendStr(x, msgXYZ); writeln('response:', v); assert( v = 'xyz ok' );

  x.Free;
end.

{ output
------------

--> LIT 2
[2]
--> LIT 3
[3, 2]
--> ADD
[5]
--> POP
[]

Result:5

--> AAAquery
response code: 123
response data: response

--> ABC
response:abc ok
--> XYZ
response:xyz ok

------------}
