@0 = internal constant [20 x i8] c"Hello LLVM-C world!!"

declare i32 @puts(i8*)

define void @main()
{
aName:
  %0 = call i32 @puts(i8* getelementptr inbounds ([20 x i8]* @0, i32 0, i32 0))
  ret void
}

