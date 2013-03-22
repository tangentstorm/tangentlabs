{ Move some data from one 64-bit register to another. }
{ This was just to verify that free pascal can indeed }
{ use 64-bit intel assembly language on linux.        }

{$asmmode intel}
program asm64;
begin
  asm
    push rax
    pop  rbx
  end
end.
