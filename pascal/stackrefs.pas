{
  Question : can you use nested procedures to build
  a recursive structure without pointers in pascal?

  Answer : nope. Below, tNode fails to compile in
  both fpc and gpc. You simply can't define a recursive
  type without using pointers ( though you can hide
  the pointers by using classes in fpc )

}
program stackrefs;
    
  type
    tNode = record
      case rank	: ( r0, r1 ) of 
        r0	: ( no : char );
        r1	: ( id : char; a, b: tNode );
      end;

  var null : tNode = ( rank: r0; no : '.' );
  function x1: tNode; begin x1.id:='x1'; x1.a:=y1; x2.b:=y2 end;
  function y1: tNode; begin y1.id:='y1'; x1.a:=y1; x2.b:=y2 end;
  function y2: tNode; begin y2.id:='y2'; x1.a:=y1; x2.b:=y2 end;
  function z1: tNode; begin z1.no:='z1' end;
  function z2: tNode; begin z2.no:='z2' end;
  function z3: tNode; begin z3.no:='z3' end;
  function z4: tNode; begin z4.no:='z4' end;

  procedure dump( node : tNode );
  begin
  end;
  
begin
  dump( x1 );
end.