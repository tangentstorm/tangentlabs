// q: delphi supports multiple default properties. does fpc?
// a: no. 'defaults.pas(14,80) Error: Only one default property is allowed'
// http://hallvards.blogspot.com/2007/09/dn4dp13-overloaded-default-array.html
{$mode delphi}
program defaults;
type
  TMultiDefaulted<T> = class
   public
    function byint( i : int32) : T; virtual; abstract;
    function bystr( s : string) : T; virtual; abstract;
    procedure toint( i :int32; v :T); virtual; abstract;
    procedure tostr( s :string; v :T); virtual; abstract;
    property ItemsByInt[Index : int32]: T read byint write toint; default;
    property ItemsByStr[const Name : string]: T read bystr write tostr; default;
  end;
begin
end.
