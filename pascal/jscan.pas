{ java scanner (=lexer/tokenizer) }
{$mode objfpc}
program jtoks;
uses sysutils, kvm;

type
  { using an interface to enable garbage collection }
  IToken = interface
    function GetText : string;
    procedure SetText( s : string );
    property text : string read GetText write SetText;
  end;
  TToken = class( TInterfacedObject, IToken )
    function GetText : string;
    procedure SetText( s : string );
    property text : string read GetText write SetText;
  private
    _text : string;
  end;
  
procedure TToken.SetText( s : string );
begin _text := s
end;

function TToken.GetText : string;
begin result := _text;
end;

{ - the lexer -------------------------------------- }

var
  ch : char;

function nextChar( out ch : char ) : char;
begin
  read( ch );
  result := ch;
end;

function next( out tok : TToken ) : TToken;
  var
    buffer : string;
  const
    alphas = ['a'..'z'] + ['A'..'Z'];
    digits = ['0'..'9'];
    alfnum = alphas + digits;
    
  procedure consume;
  begin
    buffer += ch; nextChar( ch )
  end;
  
  procedure scan_word;
  begin
    while nextChar( ch ) in alfnum do buffer += ch;
    case buffer of
      'class'     : fg( 'c' );
      'extends'   : fg( 'c' );
      'import'    : fg( 'c' );
      'package'   : fg( 'c' );
      'private'   : fg( 'c' );
      'protected' : fg( 'c' );
      'public'    : fg( 'c' );
      'return'    : fg( 'c' );
      'static'    : fg( 'c' );
      'super'     : fg( 'c' );
      'this'      : fg( 'c' );
      else if buffer[1] in ['A'..'Z'] then fg( 'W' )
      else fg( 'w' )
    end
  end;
  
  procedure scan_operator;
  begin
    fg( $6 );
    nextChar( ch );
  end;
  
  procedure scan_comment;
  var done : boolean = false;
  begin
    fg( $5 );
    case ch of
      '/' : repeat
              consume; done := ch in [#10, #13];
            until eof or done;
      '*' : repeat
              consume;
              if ch = '*' then begin
                consume; done := ch = '/';
              end;
            until eof or done;
    end;
  end;

begin
  buffer := ch;
  if ch in [ '{', '}', '(', ')', '[', ']', '.', ';' ] then
    begin fg( 'B' ); nextChar( ch ) end
  else if ch in alphas then scan_word
  else if ch = '/' then
    begin
      scan_operator;
      if ch in ['*','/'] then scan_comment
    end
  else if ch in [ '+', '-', '*', '<', '>', '=', '&', '|' ] then scan_operator
  else begin fg( 'w' ); nextChar( ch ) end;
  
  result := TToken.Create;
  result.text := buffer;
  tok := result;
end;

var tok :  TToken;
begin
  if (paramcount > 0) and fileexists( paramstr( 1 )) then
    assign( input, paramstr( 1 ));
  nextChar( ch );
  while not eof do begin
    write( Next( tok ).text )
  end;
  writeln;
end.
