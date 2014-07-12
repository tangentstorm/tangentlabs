//
// Program to illustrate some confusing behavior
// with generics and operator overloading.
//
{$mode objfpc}{$modeswitch advancedrecords}
program generic_operator_issue;

{$IFDEF import}
uses gutil;
{$ELSE}
  { TLess taken from $FPCROOT/packages/fcl-stl/src/gutil.pp}
  type
    generic TLess<T> = class
      class function c(a,b:T):boolean;inline;
      end;				      
      
      class function TLess.c(a,b:T):boolean;inline;
      begin c:=a<b;
      end;
{$ENDIF} 

{ Now we'll make a new data type that overrides < }
type
  TFoo = record
	   value : integer;
	   {$IFDEF classop}
	   class operator <(a,b: TFoo):boolean;
           {$ENDIF}
         end;

{$IFDEF classop}
class operator TFoo.<(a,b:TFoo):boolean;
{$ELSE}
operator <(a,b:TFoo):boolean;
{$ENDIF}
  begin result := a.value < b.value;
  end;

type FooLess = specialize TLess<TFoo>;

begin
end.

{ outputs
-------------------------------------------------

* case 1: local generic + unit-level operator. (OK)
  
  $ fpc gmap_op_issue.pas
  Free Pascal Compiler version 2.7.1 [2014/07/09] for x86_64
  Copyright (c) 1993-2014 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling gmap_op_issue.pas
  Linking gmap_op_issue
  48 lines compiled, 0.1 sec
  
* case 2: local generic + class operator (OK)

  fpc -dclassop gmap_op_issue.pas
  Free Pascal Compiler version 2.7.1 [2014/07/09] for x86_64
  Copyright (c) 1993-2014 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling gmap_op_issue.pas
  Linking gmap_op_issue
  48 lines compiled, 0.1 sec

* case 3 : imported generic + unit level operator (!! FAILS !!)

  $ fpc -dimport gmap_op_issue.pas
  Free Pascal Compiler version 2.7.1 [2014/07/09] for x86_64
  Copyright (c) 1993-2014 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling gmap_op_issue.pas
  Error: Operator is not overloaded: "TFoo" < "TFoo"
  gmap_op_issue.pas(49,3) Fatal: There were 1 errors compiling module, stopping
  Fatal: Compilation aborted

* case 4 : imported generic + unit level operator (OK)

  $ fpc -dimport -dclassop gmap_op_issue.pas
  Free Pascal Compiler version 2.7.1 [2014/07/09] for x86_64
  Copyright (c) 1993-2014 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling gmap_op_issue.pas
  Linking gmap_op_issue
  48 lines compiled, 0.1 sec
}
