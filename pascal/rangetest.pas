program rangetest; // does fpc do range checking at compile time?
  // answer: yes, when -O3 -vw is on.
  // adding {$R+} changes it from a warning to an error in -O3 
var x: byte; i: integer;
begin
  i:= 900; x:= i;
  // direct assignment of x:= 900; is always an error.
end.