import random

GOAL = "methinks it is like a weasel"

def random_sentence():
    # '`' comes before 'a' in the ascii character set. we'll
    # use that as a space character.
    return ''.join([chr(random.randint(ord('`'),ord('z')))
                     for i in range(len(GOAL))]).replace('a',' ')

def score_sentence(sentence):
    result = 0
    for i, char in enumerate(sentence):
        if char == GOAL[i]:
            result += 1
    return result


def main():
    score = 0
    while score <> len(GOAL):
        sentence = random_sentence()
        score = score_sentence(sentence)
        print sentence, " --> ", score

main()
