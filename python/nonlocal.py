
def make_counter(start:int=0)->int:
    count = start
    def counter()->int:
        nonlocal count
        result = count
        count += 1
        return result
    return counter


c = make_counter()
assert c() == 0
assert c() == 1



class foo: x = 1
def make_zero():
    def foo():
        return foo.x
    foo.x = 0
    return foo
zero = make_zero()
assert zero() == 0

assert zero() == 1
