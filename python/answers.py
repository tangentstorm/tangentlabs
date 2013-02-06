from json import loads
from urllib2 import urlopen
from gzip import GzipFile
from StringIO import StringIO
from itertools import groupby

kURL = 'http://api.stackoverflow.com/1.1/users/40745/answers?body=true'

def fetchAnswers():
    data = loads(GzipFile(fileobj = StringIO(urlopen(kURL).read())).read())
    return data['answers']


def parse(answers):
    for question, group in groupby(answers, lambda a: a['title']):
        answers = list(group)
        score = sum(a['score'] for a in answers)
        accepted = any(a['accepted'] for a in answers)
        yield question, accepted, score, answers
        

def format(data):
    for question, accepted, score, answers in data:
        pass

if __name__=="__main__":
    data = parse(fetchAnswers())
    for question, accepted, score, answers in data:
        print ('*' if accepted else ' '), score, question

