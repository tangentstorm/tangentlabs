# Demo of using pexpect to talk to an external process.
import sys
try: import pexpect
except: import wexpect as pexpect

# in this case we will talk to the racket read-eval-print loop
# (racket is a version of scheme from http://racket-lang.org/)

# here is the code we want racket to run:
script =[
    # define a function:
    "(define (plus a b) (+ a b))",
    # use it to make a nonsense list:
    "(list 'hello 'world (plus 7 (+ 2 9)))" ]


# now connect to the racket process and use it:
rack = pexpect.spawn('racket')


# wait for the prompt, and send some code to it:
rack.expect("> ")
rack.sendline("(+ 1 1)")
print rack.before

rack.expect("> ")
for expr in script:
    rack.sendline(expr)
    rack.expect("> ")
    sys.stdout.write(rack.before)
    sys.stdout.write(rack.after)
rack.close()

print # to force a newline after the last prompt

### Expected Output ####
"""
Welcome to Racket v5.2.1.
(define (plus a b) (+ a b))
> (list 'hello 'world (plus 7 (+ 2 9)))
'(hello world 18)
>
"""
