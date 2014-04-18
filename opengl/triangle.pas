// a simple opengl colored-triangle demonstration
// based on code from http://wiki.freepascal.org/OpenGL_Tutorial
// requires glut32.dll from http://user.xmission.com/~nate/glut.html
program triangle;
uses gl, glu, glut;


procedure DrawGLScene; cdecl;
  begin
    glClear(GL_COLOR_BUFFER_BIT or GL_DEPTH_BUFFER_BIT);
    glLoadIdentity;

     glTranslatef(0, 0, -5);
     glBegin(GL_TRIANGLES);

       glColor3f(0.25, 0, 0);
       glVertex3f(-1, -1, 0);

       glColor3f(0, 0.25, 0);
       glVertex3f(1, -1, 0);

       glColor3f(0, 0, 0.25);
       glVertex3f(0, 1, 0);
     glEnd;

    glutSwapBuffers;
  end;

procedure ReSizeGLScene(Width, Height: Integer); cdecl;
begin
  if Height = 0 then Height := 1;

  glViewport(0, 0, Width, Height);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity;
  gluPerspective(45, Width / Height, 0.1, 1000);

  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity;
end;


procedure GLKeyboard(Key : Byte; X, Y : Int32); cdecl;
  begin
    if Key = 27 then begin glutLeaveGameMode; halt(0) end;
  end;

var win : integer;
begin
  glutInit(@argc, argv);
  glutInitDisplayMode(GLUT_RGB or GLUT_DOUBLE);

  { this is how you'd make a floating window }
  //glutInitWindowPosition(0,0);
  //glutInitWindowSize(glutGet(GLUT_SCREEN_WIDTH), glutGet(GLUT_SCREEN_HEIGHT));
  //glutCreateWindow('hello world');

  { this makes a full screen window }
  glutEnterGameMode;

  glutSetCursor(GLUT_CURSOR_LEFT_ARROW);
  glClearColor(0.02, 0.02, 0.02, 0.50);

  glutDisplayFunc(@DrawGLScene);
  glutKeyboardFunc(@GLKeyboard);
  glutReshapeFunc(@ReSizeGLScene);
  glutMainLoop;

end.
