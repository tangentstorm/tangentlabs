# http://www.reddit.com/goto?id=7j1t4

def trans(s, dict):
    return ''.join(dict.get(char,char) for char in s)

assert trans('hexx0', {'x':'l', '0':'o'}) == 'hello'

PI = '3.1415926535897931'

