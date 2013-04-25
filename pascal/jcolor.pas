{$mode objfpc}{$H+}
program jcolor;
uses jscan, sysutils, kvm;

procedure ResetColor;
begin
  fg( 'w' ); bg('k')
end;

procedure OnToken( token : JToken );
begin
  ResetColor;
  case token.kind of
    jtUnknown	 : bg( 'r' );
    jtNumber	 : fg( 'R' );
    jtDelimiter	 : fg( 'B' );
    jtWhiteSpace : bg( $e9 );
    jtComment	 : fg( 'm' );
    jtName	 : fg( 'w' );
    jtKeyword	 : fg( 'c' );
    jtOperator	 : fg( 'y' );
    jtType	 : fg( 'W' );
    jtString	 : fg( 'G' );
    jtError	 : bg( 'r' );
    jtAnno	 : fg( 'g' );
    else bg('b');
  end;
  write( token.value );
end;

var
  token	  : jscan.JToken;
  scanner : jscan.JScanner;
begin
  ResetColor;
  token := JToken.Create;
  fg( 'w' ); bg('k');
  if (paramcount > 0) and fileexists( paramstr( 1 )) then begin
    assign( input, paramstr( 1 ));
    reset( input );
  end;
  scanner := JSCanner.Create;
  while not eof do OnToken( scanner.next( token ));
  ResetColor;
end.
