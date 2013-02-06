  program showenv;
    uses sysutils;
  begin

    writeln( 'path is:', getenvironmentvariable( 'PATH' ));
    
  end.
  