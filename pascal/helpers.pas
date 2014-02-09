{$mode delphi}
program helpers;
uses strutils, sysutils;

const kWhiteSpace = [#0..#32];
type
  strings = array of string;
  ThArray = record helper for strings
    function Length : cardinal;
    procedure append(s:string);
  end;
  ThString = record helper for string
    function Length : cardinal;
    function StartsWith(s:string) : boolean;
    function Capitalized : string;
    function Backwards : string;
    function Split(sep:TSysCharSet=kWhiteSpace) : strings;
  end;
  
procedure ThArray.Append(s:string);
  begin
    SetLength(self, self.length + 1);
    self[self.length-1] := s;
  end;

function ThArray.Length : cardinal;
  begin
    result := system.length(self);
  end;

function ThString.Length : cardinal;
  begin
    result := system.length(self);
  end;

function ThString.StartsWith(s : string) : boolean;
  var i : integer;
  begin
    result := s.length <= self.length;
    if result then
      for i := 1 to s.length do
        result := result and (s[i] = self[i])
  end;
  
function ThString.Split(sep:TSysCharSet=kWhiteSpace) : strings;
  var i, j : integer;
  begin
    j := wordcount(self, sep);
    setlength(result, j);
    for i := 1 to j do result[i-1] := extractword(i, self, sep);
  end;

function ThString.backwards : string;
  begin
    result := ReverseString(self);
  end;

function ThString.capitalized : string;
  begin
    result := AnsiProperCase(self, kWhiteSpace);
  end;
  
var s : string;
begin
  for s in 'once|nopu|a|emit|...'.split(['|']) do
    if s.startswith('o') then write(s.capitalized, ' ')
    else write(s.backwards,' ');
  writeln;
end.
  
{ output:
  --------------------
  Once upon a time ...
}
