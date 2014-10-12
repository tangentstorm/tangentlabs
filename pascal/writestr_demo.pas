{$mode delphiunicode}{$i xpc}
program writestr_demo;
uses xpc;
 var s : TStr = '';
begin
  s := 'will it blow up...';
  WriteStr(s, s, '.. when I do this?'); // write to s *from* s. 
  WriteLn(s);
end.
{ output (all is well).
- --------------------------------------
  will it blow up..... when I do this?
--------------------------------------- }