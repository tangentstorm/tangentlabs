{$mode objfpc}
program tracebug;
uses sysutils;
 
  procedure explode;
  begin
    raise exception.create('weak.')
  end;

begin
  try explode
  except
    system.dumpExceptionBacktrace( output )
  end
end.
