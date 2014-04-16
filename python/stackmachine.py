"""Stack machine library."""
import unittest
from string import digits

# Transitions represent actions performed when a character is
# encountered. See docstrings for StackMachine.act_xxx for details.
Transition = ([str], callable)

def STATE(ch:chr)->Transition:
    """States map input characters to transitions. This one does nothing."""
    return [], STATE

class StackMachine(object):
    def __init__(self, state):
        self.state = state
        self.queue = []         # output queue for parsed data
        self.stack = []         # stack for working on nested lists
        self.work = self.queue  # current work area (defaults to output)
        self.token = ''         # the token we're currently building

    def send(self, ch:chr):
        """Invoke state to chose transition. Perform its actions."""
        actions, self.state = self.state(ch)
        for act in actions:
            meth = act[0] if type(act) is tuple else act
            args = act[1] if type(act) is tuple else ()
            try: getattr(self, 'act_' + meth)(ch, *args)
            except AttributeError:
                raise NotImplementedError('unknown action: %s' % meth)

    def next(self)->any:
        """Return next item from queue, or None"""
        if self.queue: return self.queue.pop(0)

    def __iter__(self):
        while self.queue: yield self.next()

    #-- function interface ------------------

    def read(self, s:str)->list:
        """parse string, return all output in queue"""
        for ch in s: self.send(ch)
        self.send('\0')
        return list(self)

    #-- transition actions ------------------

    def act_drop(self, ch:chr):
        """drop the character"""
        pass

    def act_keep(self, ch:chr):
        """append character to current token"""
        self.token += ch

    def act_emit(self, ch:chr):
        """ignore character; emit and reset token"""
        self.work.append(self.token)
        self.token = ''
        
    def act_node(self, ch:chr):
        """push work list onto the stack; start new one"""
        self.stack.append(self.work)
        self.work = []

    def act_done(self, ch:chr):
        """restore previous work list with current work appended"""
        current = self.work
        self.work = self.stack.pop()
        self.work.append(current)

    #-- custom action example ------------------

    def act_to_int(self, ch:chr):
        """
        Convert the current token to a (base-10) integer, and emit it.
        This is meant to demonstrate how you can perform custom logic
        in a subclass.
        """
        self.token = int(self.token)
        self.act_emit('')


# working example : a simple s-expression parser

def do(before:[str], t:Transition)->Transition:
    actions, state = t
    return before + actions, state
    
def SX_INIT(ch:chr)->Transition:
    if   ord(ch) <= 32: return ['drop'], SX_INIT
    elif ch == '('    : return ['drop', 'node'], SX_INIT
    elif ch == ')'    : return ['drop', 'done'], SX_INIT
    elif ch in digits : return ['keep'], SX_NUMBER
    elif ch == '"'    : return ['drop'], SX_STRING
    else              : return ['keep'], SX_SYMBOL

def SX_NUMBER(ch:chr)->Transition:
    if ch in digits : return ['keep'], SX_NUMBER
    else: return do(['to_int'], SX_INIT(ch))

def SX_STRING(ch:chr)->Transition:
    if   ch == '"'  : return ['drop', 'emit'], SX_INIT
    elif ch == '\\' : return ['drop'], SX_ESCAPE
    else            : return ['keep'], SX_STRING

def SX_ESCAPE(ch:chr)->Transition:
    if   ch == 't': return SX_STRING('\t')
    elif ch == 'n': return SX_STRING('\n')
    else          : return ['keep'], SX_STRING

def SX_SYMBOL(ch:chr)->Transition:
    if ord(ch) > 32 and ch not in ('"()'): return ['keep'], SX_SYMBOL
    else: return do(['emit'], SX_INIT(ch))

class StackMachineTest(unittest.TestCase):
    def test_atoms(self):
        lisper = StackMachine(SX_INIT)
        self.assertEqual([123, 'abc'], lisper.read('123 abc'))

    def test_list(self):
        lisper = StackMachine(SX_INIT)
        self.assertEqual([[1, 2, 3]], lisper.read('(1 2 3)'))

    def test_nested(self):
        lisper = StackMachine(SX_INIT)
        self.assertEqual(
            [ [["hello (world)", 123, ['does', ['this'], 'work?']]] ],
            lisper.read('(("hello (world)" 123 (does (this) work?)))'))

if __name__=="__main__":
    unittest.main()
