{ just a test of using TFileStream with fmShareExclusive }
program filestream;
  uses sysutils, classes;
var
  f : TFileStream;
  s : String = 'hello world' + LineEnding;
begin
  f := TFileStream.Create( 'TFileStreamData.txt', fmOpenWrite or fmShareExclusive);
  f.Write(s, length(s));
  f.Free;
end.
