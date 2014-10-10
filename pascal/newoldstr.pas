//
// testing behavior of using pAnsiChar as a string type
// instead of PChar (which is 16 bits)
//
{$mode delphiunicode}{$i xpc}    // <-- new 16-bit char strings
program newoldstr;

function vTypeName(vtype:sizeint):String;
  begin
    case vtype of
      vtInteger       : result := 'vtInteger';
      vtBoolean       : result := 'vtBoolean';
      vtChar          : result := 'vtChar';
      vtExtended      : result := 'vtExtended';
      vtString        : result := 'vtString';
      vtPointer       : result := 'vtPointer';
      vtPChar         : result := 'vtPChar';
      vtObject        : result := 'vtObject';
      vtClass         : result := 'vtClass';
      vtWideChar      : result := 'vtWideChar';
      vtPWideChar     : result := 'vtPWideChar';
      vtAnsiString    : result := 'vtAnsiString';
      vtCurrency      : result := 'vtCurrency';
      vtVariant       : result := 'vtVariant';
      vtInterface     : result := 'vtInterface';
      vtWideString    : result := 'vtWideString';
      vtInt64         : result := 'vtInt64';
      vtQWord         : result := 'vtQWord';
      vtUnicodeString : result := 'vtUnicodeString';
      else result := 'unknown type';
    end
  end;

procedure emit(args:array of const);
  var arg : TVarRec;
  begin
    for arg in args do
      begin
	writeln('vtype :', vTypeName(arg.vType));
	case arg.vType of
	  // the old name 'vtPChar' is still used for 8 bit values,
	  // even though PChar is 16 bits in {$mode delphiunicode}.
	  // the embarcadero devs made the same choice:
	  // http://docwiki.embarcadero.com/RADStudio/XE7/en/Parameters_%28Delphi%29
	  vtPChar : writeln(arg.vPChar);
	  else writeln('<no printer for this vtype yet>')
	end
      end
  end;
  
var oldstr : PAnsiChar; // <-- old null-terminated 8 byte string
begin
  oldstr := 'hello my baby'; // let's see what it does.
  writeln(oldstr);           // works fine
  oldstr := 'hello my darling';
  emit([oldstr]);
end.
  