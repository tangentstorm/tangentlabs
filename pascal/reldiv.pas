{ relational algebra : division }
{$mode objfpc}
program reldiv;
uses sets;

var
  ab : array [0..5, 0..2] of byte =
	((1, 1, 4),
	 (1, 2, 4),
	 (1, 3, 4),
	 (2, 1, 0),
	 (2, 2, 0),
	 (2, 3, 0));

  b : array[0..2, 0..0] of byte =
       ((1),
	(2),
	(3));

{
         ab = a * b
    so    a = ab / a

   Here, a should be :

    ((1, 4),
     (2, 0));
}

type
  ByteArray	     = array of byte;
  TCompareByteArrays = class
    class function c( a, b : ByteArray ) : boolean;
  end;
  ByteTable	     = specialize TSet<ByteArray, TCompareByteArrays>;

{ I would prefer if this returned a value in (-1,0,1) but it doesn't }
class function TCompareByteArrays.c(a,b : ByteArray) : boolean;
  var i : cardinal = 0;
  begin
    result := length(a) <= length(b);
    while result and (i < length(a)) do
      result := a[0] < b[0];
  end;

var
  aset	: ByteArraySet;
  arows	: array of ByteArray;
  aCols	: ByteArray;
  row	: ByteArray;
  i,j	: byte;

begin
  a := ByteTable.Create();

  // the columns for @a are the columns in @ab that are not in @b
  // in this case the columns are (a0, b0, a1)
  // so @a will have two columns:
  setlength(aCols, 2);

  // and the values will come from columns 0 and 2 of @ab
  aCols[0] := 0;
  aCols[1] := 2;

  for j := 0 to high(ab) do begin

    if true then begin // TODO: test that the row actually belongs
      // append a new (empty) row:
      SetLength(arows, length(arows)+1);
      row := arows[high(arows)];
      SetLength(row, 0);

      // fill it with the data from ab:
      for i := 0 to high(aCols) do row[i] := ab[j][aCols[i]];

    end;

  for row in arows do
    begin
      for i := 0 to high(row) do write(row[i], ' ');
      writeln;
    end
end.
