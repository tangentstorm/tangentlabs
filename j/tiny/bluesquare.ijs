NB.assembly instructions for your artisinal gif
NB.(lzw img: codesize,len,4=clear,len=0,5=end)
z=:2,(#,]) 4 0 5
NB.header         10x10, 2colors, bgix, pal=blu,wht
g=:(a.i.'GIF87a'),(4$10 0),240,   0 0,  255*0 0 1,1 1 1
NB.imdsc,xy,wh,gcm,z,end
g=:g,44,(4$0),(4$10 0),0,z,59
(a.{~g)1!:2<'c:\tmp\blu.gif'
