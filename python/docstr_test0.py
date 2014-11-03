"""docstring"""         # this should get asssigned to docstr_test0.__doc__
"""second docstring"""  # this probably gets compiled to (wasted) bytecode
"""third docstring"""   # same here.

# Q: do stray docstrings get compiled to bytecode?
# to test, i created this file, and also docstr_test1.py, which replaces
# the second two docstrings with comments.
#
# A: there is a tiny overhead (1 byte per discarded string).
# but the strings themselves are optimized away.
# -------------------------------------------------------------------------------
# michal@calavera:$ python -V
# Python 2.7.8
#
# michal@calavera:$ uname -a
# FreeBSD calavera 9.2-RELEASE FreeBSD 9.2-RELEASE #0 r255898: Thu Sep 26 22:50:31 
#   UTC 2013     root@bake.isc.freebsd.org:/usr/obj/usr/src/sys/GENERIC  amd64
#
# michal@calavera:$ python -c'import docstr_test0, docstr_test1'
#
# michal@calavera:$ ll docstr_test?.pyc
# -rw-r--r--  1 michal  michal  136 Nov  3 04:29 docstr_test0.pyc
# -rw-r--r--  1 michal  michal  134 Nov  3 04:29 docstr_test1.pyc
#
# michal@calavera:$ hexdump -C docstr_test0.pyc
# 00000000  03 f3 0d 0a e8 58 57 54  63 00 00 00 00 00 00 00  |.....XWTc.......|
# 00000010  00 01 00 00 00 40 00 00  00 73 0a 00 00 00 64 00  |.....@...s....d.|
# 00000020  00 5a 00 00 64 01 00 53  28 02 00 00 00 74 09 00  |.Z..d..S(....t..|
# 00000030  00 00 64 6f 63 73 74 72  69 6e 67 4e 28 01 00 00  |..docstringN(...|
# 00000040  00 74 07 00 00 00 5f 5f  64 6f 63 5f 5f 28 00 00  |.t....__doc__(..|
# 00000050  00 00 28 00 00 00 00 28  00 00 00 00 73 0f 00 00  |..(....(....s...|
# 00000060  00 64 6f 63 73 74 72 5f  74 65 73 74 30 2e 70 79  |.docstr_test0.py|
# 00000070  74 08 00 00 00 3c 6d 6f  64 75 6c 65 3e 03 00 00  |t....<module>...|
# 00000080  00 73 02 00 00 00 06 02                           |.s......|
# 00000088
#
# michal@calavera:$ hexdump -C docstr_test1.pyc
# 00000000  03 f3 0d 0a aa 57 57 54  63 00 00 00 00 00 00 00  |.....WWTc.......|
# 00000010  00 01 00 00 00 40 00 00  00 73 0a 00 00 00 64 00  |.....@...s....d.|
# 00000020  00 5a 00 00 64 01 00 53  28 02 00 00 00 74 09 00  |.Z..d..S(....t..|
# 00000030  00 00 64 6f 63 73 74 72  69 6e 67 4e 28 01 00 00  |..docstringN(...|
# 00000040  00 74 07 00 00 00 5f 5f  64 6f 63 5f 5f 28 00 00  |.t....__doc__(..|
# 00000050  00 00 28 00 00 00 00 28  00 00 00 00 73 0f 00 00  |..(....(....s...|
# 00000060  00 64 6f 63 73 74 72 5f  74 65 73 74 31 2e 70 79  |.docstr_test1.py|
# 00000070  74 08 00 00 00 3c 6d 6f  64 75 6c 65 3e 02 00 00  |t....<module>...|
# 00000080  00 73 00 00 00 00                                 |.s....|
# 00000086
