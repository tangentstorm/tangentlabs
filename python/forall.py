#!/usr/bin/python
import os, sys

cmd = " ".join(sys.argv[1:])
if cmd:
    for line in os.popen("find . -type d -maxdepth 1 -mindepth 1"):
        d = line[:-1]
        if os.path.exists(d + "/CVS"):
            os.chdir(d)
            print "####", d, "####"
            os.system(cmd)
            os.chdir("..")
else:
    print "usage:  %s command" % sys.argv[0]
            
            
