program fsmtok(input);

// demo program to tokenize input using a finite state machine.
// in an antlr-like notation, the syntax would look like this:
//
//  Alpha    : [ 'A' .. 'Z' ] | [ 'a' .. 'z' ] ;
//  Digit    : [ '0' .. '9' ] ;
//  LBrace   : '{' ;
//  RBrace   : '}' ;
//  Quote    : '"' ;
//  EasyOp   : '+' | '-' | '*' | '/' | '%' | '=' ;
//  NUMBER   : Digit+ ;
//  IDEN     : Alpha (Alpha | Digit )*  ;
//  COMMENT  : LBrace (~ RBrace)* RBrace ;
//  OPERATOR : EasyOp | (( '<' | '>' ) '=' ? )

// the fsm looks like this:
//
//          +--------+--------+--------+--------+--------+--------+
//          | space  | digit  | alpha  | ezop   |  '<'   |  '>'   |
// +--------+--------+--------+--------+--------+--------+--------+
// | INIT   |  INIT  | -NUM   | -VAR   |        |  LT    |  GT    |
// | NUM    | ^INIT  | +NUM   | ERR@   |        |        |        |
// | LT     |        |        |        |        |        |        |
// | GT     |        |        |        |        |        |        |
// +--------+--------+--------+--------+--------+--------+--------+

//     Alpha  -> Goto IDENT
//     Quote  -> Goto STRING
//     LBrace -> Goto SIMPLE 
//     RBrace -> Goto SIMPLE
//     Opers  -> Goto SIMPLE


type
  { input symbols are grouped characters }
  { the group tag is just a character that exemplifies the group. }
  TCharGroup = [ ' ', 'a', '0', '+', '(', ')', '<', '>', '{', '}' ];
  TSymbol = record
    tag : TCharGroup;
    val : char;
  end;
  
  { output tokens are tagged tokens }
  TTokTag =  ( ttNumber, ttString, ttIden, ttOperator, ttComment,
               ttSPACE, ttLBRACK, ttRBRACK, ttLPAREN, ttRPAREN );
  TToken = record
    tag : TTokTyp;
    val : string;
  end;
  
  { internal transitions are encoded as actions }
  
  TOpCode = ( opEmit, opSkip,
              opGoto, opGosub, opReturn );
  
  { okay so it's a push-down automaton instead of a
    finite state machine. deal with it. :) }
  
  TAction = record case opcode : TOpcode of
    opEmit   : ( tag : TTokTyp );
    opSkip,
    opReturn : ( );
    opGoto,
    opGoSub  : ( state : cardinal );
  end;
  
  TScript = array of TAction;
  TCharGrouper  = function( ch : char ) : TGroupedChar;
  TTokenHandler = procedure( tok : TToken );

type TFSM = class
  _OnToken : TTokenHandler;
  _actions : array of TAction;
  procedure consume( ch : char );
  procedure consume(  s : string );
  property OnToken : TTokenHandler read _OnToken;
end;

{ application - specific stuff }

const kColors : array [TTokTyp] of char =
  [ {ttnumber}   'Y',   {ttstring}  'G', {ttiden} 'w',
    {ttoperator} 'W',   {ttcomment} 'K', {ttspace} 'k',
    { [ / ] } 'B', 'B', { ( / ) } 'C', 'C' ];

procedure EmitToken( tok : TToken );
  begin kvm.fg(kColors[tok.tag]); write(tok.val);
  end;
  
function nextchar: char;
  begin read(input, result);
  end;
  
begin
  fsm := TFSM.Create;
  fsm.OnToken := EmitToken;
  while not eof(input) do fsm.consume(nextchar);
  fsm.free;
end.
