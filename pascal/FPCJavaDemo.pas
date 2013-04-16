{ Simple FPC Java Demo.
  
  written 16 april 2013 by tangentstorm, with help from this thread:
  http://www.hu.freepascal.org/lists/fpc-pascal/2012-January/031830.html
  This code is in the public domain.

  To get ppjvm:
  -------------
  - in theory: http://wiki.freepascal.org/FPC_JVM/Building
    (but i couldn't get that working on x86_64-linux with fpc 2.6.2)
  
  - instead, I just used the "crossbuild" menu in CodeTyphon
    and it built the jvm-java crossbuilder for me.

  To run this demo:
  -----------------
  $ ppcjvm -XP FPCJavaDemo.pas
  Generated:./TJavaDemo.class
  Generated: ./FPCJavaDemo.class
  Warning: Object system.class not found, Linking may fail !
  $ # You can safely ignore the above warning.
  $ [java -cp .:/usr/lib/codetyphon/fpc/units/jvm-java/rtl/ FPCJavaDemo
  hello world!
  $

}
{$mode objfpc}
program FPCJavaDemo;
uses jdk15; { <- that's all that comes with fpc, but see the javapp tool }
  
type
  TJavaDemo = class
    constructor Create;
    function Hello : UnicodeString;
  end;

constructor TJavaDemo.Create;
begin
end;

function TJavaDemo.Hello : UnicodeString;
begin
  result := 'hello world!'
end;

var
  jd : TJavaDemo;
begin
  jd := TJavaDemo.Create;
  jlsystem.fout.println( jd.Hello );
end.
