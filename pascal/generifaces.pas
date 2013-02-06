{$mode objfpc}
unit generifaces;
{ Unit to demonstrate that free pascal does not complain
  when generic types promise to implement an interface but
  then do not. }
interface
  
  type
    IFoo = interface
      function foo : byte;
    end; 
	 
    generic GBar<t>= class( TInterfacedObject, IFoo )
      // does not implement foo, but compiler doesn't care. 
    end;						    
	 
    TBar = class( TInterfacedObject, IFoo )
      // does not implement foo, and compiler complains	
    end;						

    // it does complain when you attempt to specialize it though:
    SBar =  specialize GBar<Integer>;

implementation
end.
