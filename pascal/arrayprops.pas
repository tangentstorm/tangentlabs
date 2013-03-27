{ Array properties in Free Pascal.
  Array properties are properties that allow subscripting.

  The following example creates a 2D grid (matrix)
  type and populates it with values. Note that the
  underlying array (TGrid.data) is one-dimensional.
}
{$mode objfpc}
program arrayprops;

type
  generic TGrid<T> = class
  private
    _w, _h : cardinal;
    data : array of T;
    procedure SetItem( x, y : cardinal; value : T );
    function GetItem( x, y : cardinal ) : T;
  public
    constructor Create;
    constructor Create( w, h : cardinal );
    destructor Destroy; override;
    property at[ x, y : cardinal ]: T read GetItem write SetItem; default;
  end;
  
constructor TGrid.Create;
begin
  Create(16,16);
end;

constructor TGrid.Create( w, h : cardinal );
begin
  _w := w; _h := h;
  SetLength(data, w*h);
end;

procedure TGrid.SetItem( x, y : cardinal; value : T );
begin
  data[ y * _w + x ] := value;
end;

function TGrid.GetItem( x, y : cardinal ) : T;
begin
  result := data[ y * _w + x ];
end;

destructor TGrid.Destroy;
begin
  data := nil;
end;

{ -------------------------- }

type
  THexCode = string[2];
  THexGrid = specialize TGrid<THexCode>;
const
  hex ='0123456789ABCDEF';
var
  x, y  : byte;
  codes : THexGrid;
begin
  codes := THexGrid.Create;
  for y := $0 to $F do for x := 0 to $F do
    codes[ x, y ] := hex[x+1] + hex[y+1];

  for y := $0 to $F do
  begin
    for x := 0 to $E do write(codes[ x, y ], ' ');
    writeln(codes[$f, y]);
  end
end.

{
  output:

  00 10 20 30 40 50 60 70 80 90 A0 B0 C0 D0 E0 F0
  01 11 21 31 41 51 61 71 81 91 A1 B1 C1 D1 E1 F1
  02 12 22 32 42 52 62 72 82 92 A2 B2 C2 D2 E2 F2
  03 13 23 33 43 53 63 73 83 93 A3 B3 C3 D3 E3 F3
  04 14 24 34 44 54 64 74 84 94 A4 B4 C4 D4 E4 F4
  05 15 25 35 45 55 65 75 85 95 A5 B5 C5 D5 E5 F5
  06 16 26 36 46 56 66 76 86 96 A6 B6 C6 D6 E6 F6
  07 17 27 37 47 57 67 77 87 97 A7 B7 C7 D7 E7 F7
  08 18 28 38 48 58 68 78 88 98 A8 B8 C8 D8 E8 F8
  09 19 29 39 49 59 69 79 89 99 A9 B9 C9 D9 E9 F9
  0A 1A 2A 3A 4A 5A 6A 7A 8A 9A AA BA CA DA EA FA
  0B 1B 2B 3B 4B 5B 6B 7B 8B 9B AB BB CB DB EB FB
  0C 1C 2C 3C 4C 5C 6C 7C 8C 9C AC BC CC DC EC FC
  0D 1D 2D 3D 4D 5D 6D 7D 8D 9D AD BD CD DD ED FD
  0E 1E 2E 3E 4E 5E 6E 7E 8E 9E AE BE CE DE EE FE
  0F 1F 2F 3F 4F 5F 6F 7F 8F 9F AF BF CF DF EF FF
}
