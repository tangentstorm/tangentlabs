program termsize;
uses baseunix, termio;

var
  w, h : word; { terminal width and height }

procedure UpdateTermSize;
  var winsize : termio.TWinSize;
  begin
    baseunix.fpioctl(system.stdinputhandle,
		     termio.TIOCGWINSZ,
		     @winsize);
    termsize.w := winsize.ws_row;
    termsize.h := winsize.ws_col;
  end;


{--- example ------- }

procedure OnResize( sig : cint ); cdecl;
  begin
    UpdateTermSize;
    WriteLn( 'The terminal size is: ', w, ' x ', h, '.' );
  end;

begin
  OnResize( 0 );

  { callback for window/terminal size change }
  if baseunix.fpSignal( baseunix.SigWinCh,
		        baseunix.SignalHandler( @OnResize ))
     = baseunix.signalhandler(SIG_ERR)
  then
    begin
      writeln('Error: ',fpGetErrno,'.');
      halt(1);
    end;

  WriteLn( 'Resize Terminal, or press enter to exit.' );
  ReadLn;

end.
