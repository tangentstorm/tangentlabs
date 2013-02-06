{

  1106.2012
  
  this program was provided [ oct 11 2012 ] in #fpc
  by a guy named andax.

  he observed some odd behavior with for loops when the
  number is supplied via Readln, and was worried about
  security implications... turns out the issue was just
  that he was typing numbers that were too big to fit in
  the specified type, and wasn't checking for that.

}


{ andax : yes, when i type 30000, it does count. When i type 40000 it does not count. When i type 1000000 it does count until 16960. }


program ZAEHL;
  VAR i: integer;
  VAR Endzahl: integer;
    (*Im Beispielprogramm http : //www.willemer.de/informatik/lang/pascal.htm fehlte hier die zweite Variable*)
BEGIN
  Write ('Wie weit soll ich zaehlen?');
  Readln(Endzahl);
  Writeln('Endzahl ist:', endzahl );
  Readln;
  FOR i:=1 TO Endzahl DO
    Writeln(i);
END.
