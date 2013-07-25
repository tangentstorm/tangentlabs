// 25-jul-2013.
//
// Kaco on #fpc reported an EAbstractError when a grand-subclass
// called an overridden abstract method. The question is: does the
// intermediate subclass need to implement the abstract method so
// the grand subclass can override it?
//
// My hypothesis is that the answer is no. Experiment follows:
{$mode objfpc}
program abstractgrandmethod;

type
  TGrandParent = class (TObject)
    procedure method; virtual; abstract;
  end;
  TParent = class (TGrandParent)
  end;
  TChild = class (TParent)
    procedure method; override;
  end;


procedure TChild.method;
  begin
    writeln('here i come to save the day.')
  end;


var mighty : TGrandParent;
begin
  mighty := TChild.Create;
  mighty.method;
end.

{ output:
-----------------------------
here i come to save the day.
-----------------------------

  Conclusion.
  The hypothesis is supported.
  The middle class does not need to implement an abstract
  method before a grandchild class can override it.
}
