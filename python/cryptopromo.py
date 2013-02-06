"""
It's time to test your brainpower! I will give
six months of free web hosting to the first person
to solve this cryptogram. Can you figure it out?

Since you have taken my challenge and decrypted
the secret message, I will even give you the
cryptogram-making source code to amaze your
friends!
"""
import sys, string, random
cipher = list(string.letters[:26])
random.shuffle(cipher)
cipher = "".join(cipher)
cipher += cipher.upper()
map = {}
for plain, crypt in zip(string.letters, cipher):
    map[plain] = crypt
for line in open(sys.argv[1]):
    print "".join([map.get(ch,ch) for ch in line])[:-1]
