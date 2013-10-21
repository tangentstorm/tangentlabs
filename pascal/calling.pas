// a test of the pascal calling conventions
// this doesn't do much on freebsd for x64..
{$mode objfpc}
program calling;
{$packrecords 1}
type
  int      = QWord;
  PInt     = ^int;
  T4IntRec = packed record w, x, y, z : int end;
  T4IntAry = array[0..3] of int;
  Tf5ItoI  = function(a,b,c,d,e : int) : int;
  Tf4ItoI  = function(a,b,c,d : int) : int;
  TfRecToI = function(rec : T4IntRec) : int;
  TfAryToI = function(rec : T4IntAry) : int;
  
function f4IToI(a, b, c, d : int) : int;
  var p : PInt;
  begin
    p := @a; dec(p);
    write('^: ', p^, ' a: ', a, ' b: ', b, ' c: ', c, ' d: ', d, ' ');
    p := @d; inc(p);
    write('^: ', p^, ' ');
    result := a + b + c + d;
  end;

function f5IToI(a, b, c, d, e : int) : int;
  var p : PInt;
  begin
    p := @a; dec(p);
    write('^: ', p^, ' a: ', a, ' b: ', b, ' c: ', c, ' d: ', d, ' e: ', e, ' ');
    p := @e; inc(p);
    write('^: ', p^, ' ');
    result := a + b + c + d;
  end;
  

var
  rec   : T4IntRec;
  ary   : T4IntAry;
  fint  : Tf4IToI;
  fint5 : Tf5IToI;
  frec  : TfRecToI;
  fary  : TfAryToI;
  i     : int;
begin
  with rec do begin w := 0; x := 1; y := 2; z := 3 end;
  for i := 0 to 3 do ary[i]:=i;
  fint := @f4ItoI;
  i := fint(rec.w, rec.x, rec.y, rec.z);
  writeln('-> ', i);
  frec := TFRecToI(fint); writeln('-> ', frec(rec));
  fary := TFAryToI(fint); writeln('-> ', fary(ary));
end.
