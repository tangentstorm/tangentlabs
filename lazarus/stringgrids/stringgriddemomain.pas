unit stringgriddemomain;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, odbcconn, sqlite3conn, sqldb, DB, FileUtil, RTTIGrids,
  Forms, Controls, Graphics, Dialogs, Grids, StdCtrls, DBCtrls, DBGrids;

type

  { TForm1 }

  TForm1 = class(TForm)
    dsSyms: TDatasource;
    dsFiles: TDatasource;
    grFiles: TDBGrid;
    grSyms: TDBGrid;
    DBMemo1: TDBMemo;
    DBNavigator1: TDBNavigator;
    dbc: TSQLite3Connection;
    qFiles: TSQLQuery;
    qFilescontent: TMemoField;
    qFilesfilename: TStringField;
    qFilesid: TLongintField;
    qSyms: TSQLQuery;
    txn: TSQLTransaction;
    procedure grFilesEditingDone(Sender: TObject);
    procedure FormClose(Sender: TObject; var CloseAction: TCloseAction);
    procedure FormCreate(Sender: TObject);
    procedure qFilesAfterPost(DataSet: TDataSet);
    procedure qFilesAfterScroll(DataSet: TDataSet);
  private
    { private declarations }
  public
    { public declarations }
    procedure SaveChanges;
  end;

var
  Form1: TForm1;

implementation

{$R *.lfm}

{ TForm1 }

procedure TForm1.FormCreate(Sender: TObject);
begin
  dbc.Open;
  txn.Active := True;
  qFiles.Open;
  qSyms.Open;
  txn.CommitRetaining;
end;

procedure TForm1.qFilesAfterPost(DataSet: TDataSet);
begin
  SaveChanges;
end;

procedure TForm1.qFilesAfterScroll(DataSet: TDataSet);
begin
//  qSyms.ParamByName('');
end;

procedure TForm1.SaveChanges;
begin
  qFiles.ApplyUpdates;
  txn.CommitRetaining;
end;

procedure TForm1.FormClose(Sender: TObject; var CloseAction: TCloseAction);
begin
  SaveChanges;
end;

procedure TForm1.grFilesEditingDone(Sender: TObject);
begin
  SaveChanges;
end;

end.

