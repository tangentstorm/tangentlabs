-- basic io demo

def chomp (s : String) := s.trimRight

def main : IO Unit := do
  (← IO.getStdout).putStr "name> "
  let input := chomp (← (← IO.getStdin).getLine)
  IO.println s!"Hello, {input}!"
