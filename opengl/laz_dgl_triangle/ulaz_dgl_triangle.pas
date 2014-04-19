// demo for using dglOpenGL on ms-windows in lazarus
//
// based on code from:
//   - http://wiki.delphigl.com/index.php/Tutorial_Lektion_1
//   - http://wiki.freepascal.org/OpenGL_Tutorial
//
// note: any name that starts with 'gl' is defined in dglOpenGL.pas
unit ulaz_dgl_triangle;

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, FileUtil, Forms, Controls, Graphics, Dialogs, ExtCtrls,
  windows, dgl in '../dglOpenGL.pas';

type

  { TForm1 }

  TForm1 = class(TForm)
    Timer1: TTimer;
    procedure FormCreate(Sender: TObject);
    procedure Timer1Timer(Sender: TObject);
  private
    { private declarations }
  public
    { public declarations }
  end;

var
  Form1: TForm1;
  dc,rc : windows.HDC;

implementation

{$R *.lfm}

{ TForm1 }

procedure TForm1.FormCreate(Sender: TObject);
  begin
    dgl.InitOpenGL;
    dc := windows.GetDC(self.Handle);
    rc := dgl.CreateRenderingContext(
              dc,
              [dgl.opDoubleBuffered],
              32,   // colorbits
              24,   // zbits
              0,    // stencilbits
              0,    // accumbits
              0,    // auxbuffers
              0 );  // layer

    dgl.ActivateRenderingContext( dc, rc );

    glViewport( 0, 0, self.ClientWidth, self.ClientHeight );
    glMatrixMode( GL_PROJECTION ); glLoadIdentity;
    gluPerspective( 60, self.ClientWidth / self.ClientHeight, 0.1, 100 );

    glClearColor(0.00, 0.00, 0.00, 1.0);
    glMatrixMode( GL_MODELVIEW ); glLoadIdentity;
  end;

procedure TForm1.Timer1Timer(Sender: TObject);
  begin
    glClear(GL_COLOR_BUFFER_BIT or GL_DEPTH_BUFFER_BIT);
    glLoadIdentity; glTranslatef(0, 0, -5);
    glBegin( GL_TRIANGLES );
      glColor3f(0.50, 0, 0); glVertex3f(-1, -1, 0);
      glColor3f(0, 0.50, 0); glVertex3f(1, -1, 0);
      glColor3f(0, 0, 0.50); glVertex3f(0, 1, 0);
    glEnd;
    windows.SwapBuffers(dc);
  end;

end.

