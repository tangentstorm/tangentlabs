NB. patches required to make J work on FreeBSD64

cc'z'

NB. TODO: drop non-freebsd values from this mess

UNXLIB=: ([: <;._1 ' ',]);._2 (0 : 0)
libc.so.6 libc.so libc.so.7 libc.dylib libc.dylib
libz.so.1 libz.so libc.so.7 libz.dylib libz.dylib
libsqlite3.so.0 libsqlite.so libsqlite3.so libsqlite3.dylib libsqlite3.dylib
libxml2.so.2 libxml2.so libxml2.so libxml2.dylib libxml2.dylib
)
unxlib=: 3 : 0
r=. (;: 'c z sqlite3') i. <,y
c=. IFIOS + (;: 'Linux Android FreeBSD Darwin') i. <UNAME_z_
(<r,c) {:: UNXLIB_z_
)
