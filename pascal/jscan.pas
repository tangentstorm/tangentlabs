{ java scanner (=lexer/tokenizer)
  see jcolor.pas for example usage. }
{$mode objfpc}{$H+}
unit jscan;
interface

type
  JTokenID = ( jtNumber, jtOperator, jtString, jtAnno,
               jtComment, jtWhiteSpace, jtDelimiter,
	       jtType, jtName, jtValue, jtKeyword,
	       jtUnknown, jtError );

  generic GScanner<tokT> = class
    constructor Create;
  private
    ch    : char;
    token : tokT;
    procedure Consume;
  end;

  JToken = class
    kind  : JTokenID;
    value : string
  end;

  JScanner = class (specialize GScanner<JToken>)
    function Next( tok : JToken ) : JToken;
  end;

implementation

constructor GScanner.Create;
  begin
    read( ch );
  end;

procedure GScanner.Consume;
  begin
    token.value += ch; read( ch );
  end;

function JScanner.Next( tok  : JToken ) : JToken;

  const
    alphas = ['a'..'z'] + ['A'..'Z'] + ['_'];
    digits = ['0'..'9'];
    octals = ['0'..'7'];
    hexals = digits + ['A'..'F'] + ['a'..'f'];
    alfnum = alphas + digits;

  procedure scan_number;
    var
      accept : set of char = digits;
      done   : boolean = false;
    begin
      if ch = '0' then begin
	consume;
	if ch = 'x' then accept := hexals
	else if ch in octals then accept := octals
	else if ch in digits then token.kind := jtError
	else done := true
      end;
      if not done then repeat consume until not (ch in accept);
      // TODO: decimal point, scientific notation
      token.kind := jtNumber;
    end;

  procedure scan_word;
    begin
      repeat consume until not (ch in alfnum);
      case token.value of
	{ keywords }
	'class', 'do', 'else', 'extends', 'for', 'if', 'import',
	'new', 'package', 'private', 'protected', 'public', 'return',
	'static', 'switch', 'while' : token.kind := jtKeyword;

	{ special values }
	'false', 'null', 'super', 'this', 'true' : token.kind := jtValue;

	{ types }
	'void',  'boolean', 'int', 'long', 'word', 'byte',
	'char', 'float', 'double' : token.kind := jtType;
	else if token.value[1] in ['A'..'Z'] then token.kind := jtType
	else token.kind := jtName;
      end
    end;

  procedure scan_operator;
    begin
      consume;
      token.kind := jtOperator;
    end;

  procedure scan_string;
    begin
      repeat
	consume;
	if ch = '\' then begin consume; consume end;
      until ch = '"';
      consume;
      token.kind := jtString;
    end;

  procedure scan_comment;
    var done : boolean = false;
    begin
      case ch of
	'/' : repeat consume until eof or ( ch in [#10, #13]);
	'*' : repeat
		consume;
		if ch = '*' then begin
		  consume; done := ch = '/';
		end
	      until eof or done;
      end;
      consume;
      token.kind := jtComment;
    end;

  procedure scan_whitespace;
    begin
      repeat consume until eof or (ch > #32);
      token.kind := jtWhiteSpace;
    end;

  procedure scan_delimiter;
    begin consume; token.kind := jtDelimiter;
    end;

  begin
    token := tok;
    token.value := '';
    token.kind := jtUnknown;
    case ch of
      #0 .. #32 : scan_whitespace;
      '{', '}', '(', ')', '[', ']', '.', ';', ',' : scan_delimiter;
      '0'..'9' : scan_number;
      '"' : scan_string;
      '@' : begin consume; scan_word; token.kind := jtAnno end;
      '/' : begin scan_operator; if ch in ['*','/'] then scan_comment end;
      '+', '-', '*', '<', '>', '=', '&', '|', '!', '?', ':' : scan_operator;
      else
	if ch in alphas then scan_word
	else begin consume; token.kind := jtError end
    end;

    result := token;
  end;

end.
