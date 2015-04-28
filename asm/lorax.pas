{$asmmode intel}
program lorax;
// "i am the lorax. i speak for the trees"..
// this program tests the effects of assigning to eax
// (which is the lower 32 bits of the 64 bit rax register)
// on the value currently in rax.
var r:UInt64=$0011223344556677; e:UInt32=$FFEEDDCC;
begin
  asm
    mov rax, r
    mov eax, e
    mov r, rax
  end;
  writeln(hexstr(r,16));
end.
// output:
// 00000000FFEEDDCC
