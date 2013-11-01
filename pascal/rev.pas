// algorithms to reverse a string
{$mode objfpc}
program rev;
uses sysutils; // for RightStr;

function RevCopy(s : string) : string;
  var i, len : cardinal;
  begin
    len := Length(s);
    SetLength(result, len);
    for i := len downto 1 do result += s[i];
  end;

function RevInplace(s : string) : string;
  var len, mid, i : cardinal; tmp : char;
  begin
    len := Length(s);
    mid := len div 2;
    for i := 0 to mid-1 do
      begin
	tmp := s[i+1];
	s[i+1] := s[len - i];
	s[len - i] := tmp;
      end;
    result := s;
  end;
  
function RevRecurse(s : string) : string;
  var len : cardinal;
  begin
    len := length(s);
    if len in [0, 1] then result := s
    else result := RevRecurse(RightStr(s, len-1)) + s[1];
  end;

var s : string = '!dlrow olleh';
begin
  WriteLn('original   : ', s);
  WriteLn('RevCopy    : ', RevCopy(s));
  WriteLn('RevInplace : ', RevInplace(s));
  WriteLn('RevRecurse : ', RevRecurse(s));
  WriteLn('original   : ', s);
end.
