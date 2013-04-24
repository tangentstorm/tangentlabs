{ java scanner (=lexer/tokenizer) }
{$mode objfpc}{$H+}
program jtoks;
uses sysutils, kvm;

var
  ch : char;

{ scanner }
function next : string;
  var buffer : string = '';
  const
    alphas = ['a'..'z'] + ['A'..'Z'] + ['_'];
    digits = ['0'..'9'];
    octals = ['0'..'7'];
    hexals = digits + ['A'..'F'] + ['a'..'f'];
    alfnum = alphas + digits;

  procedure consume;
  begin
    buffer += ch; read( ch );
  end;

  procedure scan_number;
  var
    accept : set of char = digits;
    done   : boolean = false;
  begin
    if ch = '0' then begin
      consume;
      if ch = 'x' then accept := hexals
      else if ch in octals then accept := octals
      else if ch in digits then bg('r') // error
      else done := true
    end;
    if not done then repeat consume until not (ch in accept);
    // TODO: decimal point, scientific notation
    fg( 'R' );
  end;

  procedure scan_word;
  begin
    repeat consume until not (ch in alfnum);
    case buffer of
      { keywords }
      'class', 'do', 'else', 'extends', 'for', 'if', 'import',
      'new', 'package', 'private', 'protected', 'public', 'return',
      'static', 'switch', 'while' : fg('c');

      { special values }
      'false', 'null', 'super', 'this', 'true' : fg( 'C' );

      { types }
      'void',  'boolean', 'int', 'long', 'word', 'byte',
      'char', 'float', 'double' : fg( 'W' );
      else if buffer[1] in ['A'..'Z'] then fg( 'W' )
      else fg( 'w' )
    end
  end;

  procedure scan_operator;
  begin
    consume; fg( 'y' );
  end;

  procedure scan_string;
  begin
    repeat
      consume;
      if ch = '\' then begin consume; consume end;
    until ch = '"';
    consume; fg( 'G' );
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
    consume; fg( 'm' );
  end;

  procedure scan_whitespace;
  begin
    repeat consume until eof or (ch > #32);
    bg( $e9 );
  end;

  procedure scan_delimiter;
  begin consume; fg( 'B' )
  end;

begin
  bg( 'k' );
  case ch of
    #0 .. #32 : scan_whitespace;
    '{', '}', '(', ')', '[', ']', '.', ';', ',' : scan_delimiter;
    '0'..'9' : scan_number;
    '"' : scan_string;
    '@' : begin consume; scan_word; fg('g') end;
    '/' : begin scan_operator; if ch in ['*','/'] then scan_comment end;
    '+', '-', '*', '<', '>', '=', '&', '|', '!', '?', ':' : scan_operator;
  else
    if ch in alphas then scan_word
    else begin bg( 'r' ); consume end
  end;
  result := buffer;
end;

begin
  if (paramcount > 0) and fileexists( paramstr( 1 )) then begin
    assign( input, paramstr( 1 )); reset( input );
  end;
  read( ch );
  while not eof do write( next );
  fg( 'w' ); bg('k')
end.
