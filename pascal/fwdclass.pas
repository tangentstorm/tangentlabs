{$mode objfpc}
program fwd;

  type
    TFoo = class(TObject); // not a forward declaration!
    TFoo = class(TObject) procedure Bar; end;

  var foo : TFoo;
begin
  foo := TFoo.create;
end.
