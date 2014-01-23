unit udockingdemo;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, FileUtil, Forms, Controls, Graphics, Dialogs, ExtCtrls,
  StdCtrls;

type

  { TForm1 }

  TForm1 = class(TForm)
    Button1: TButton;
    DraggableDock: TPanel;
    MainDock: TPanel;
    sq1: TPanel;
    Panel8: TPanel;
    sq2: TPanel;
    sq3: TPanel;
    sq4: TPanel;
    procedure box1ChangeBounds(Sender: TObject);
    procedure Button1Click(Sender: TObject);
    procedure Edit1Change(Sender: TObject);
    procedure FormCreate(Sender: TObject);
    procedure Memo1DblClick(Sender: TObject);
    procedure Memo1Exit(Sender: TObject);
  private
    { private declarations }
  public
    { public declarations }
  end;

var
  Form1: TForm1;

implementation

{$R *.lfm}

{ TForm1 }

procedure TForm1.box1ChangeBounds(Sender: TObject);
begin

end;

procedure TForm1.Button1Click(Sender: TObject);
var
  panel: TPanel;
begin
  panel := TPanel.Create(self);
  panel.DragMode := dmAutomatic;
  panel.DragKind := dkDock;
  panel.DockSite := False;
  panel.color := $0034D9F5;
//  panel.align := alCustom;
  panel.Width := 120;
  panel.Height := 42;
  panel.left := 0;
  panel.top := 0;
  panel.Constraints.MinWidth := 120;
  panel.Constraints.MinHeight := 50;
  panel.Constraints.MaxWidth := 120;
  panel.Constraints.MaxHeight := 50;
  panel.Caption := 'card';
  panel.parent := self;
end;

procedure TForm1.Edit1Change(Sender: TObject);
begin

end;

procedure TForm1.FormCreate(Sender: TObject);
var
  i: integer;
  pan: TPanel;
  sc: TSizeConstraints;
begin
end;

procedure TForm1.Memo1DblClick(Sender: TObject);
var
  memo: TMemo;
begin
  memo := Sender as TMemo;
  memo.ReadOnly := False;
  memo.HideSelection := False;
end;

procedure TForm1.Memo1Exit(Sender: TObject);
var
  memo: TMemo;
begin
  memo := Sender as TMemo;
  memo.ReadOnly := True;
  memo.HideSelection := True;
end;

end.
