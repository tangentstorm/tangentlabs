{$H+} // enable long strings by default
program LengthVsSizeOf;

  var
    a : string;      // long string
    b : string[255]; // old-style string	       
  
begin
  a := 'object';
  b := 'pascal';

  writeln('new strings: ', a, ' size:', sizeof(a), ' length: ', length(a));
  writeln('old strings: ', b, ' size:', sizeof(b), ' length: ', length(b));

end.


output:
-------
new strings: object size:8 length: 6
old strings: pascal size:256 length: 6

