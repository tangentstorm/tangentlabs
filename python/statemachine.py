if True:

    ## a generic state machine framework ###################
    
    class Message(object):
        """
        This represents a message being passed to the
        state machine.
        """
        def __init__(self, name):
            self.name = name
        def __str__(self):
            return "Message(%r)" % self.name
        def __call__(self, smap):
            try:
                return smap[self]
            except KeyError:
                raise Exception("invalid message: %s vs %s"
                                % (self, smap))

    class MessageFactory(object):
        """
        Since python doesn't have symbols, this automagically
        creates the messages for you. (It's purely for
        convenience, and you could just as easily instantiate
        each message by hand.
        """
        cache = {}
        def __getattr__(self, name):
            return self.cache.setdefault(name, Message(name))

    class StateMachine(object):
        """
        This keeps track of the work.
        """
        def __init__(self, state):
            self.state = state
        def __call__(self, msg):
            self.state = self.state(msg)


    ## how to set it up: ###################################

    msg = MessageFactory()
    state =\
    {
        0 : lambda m: m({ msg.A : state[1],
                          msg.B : state[2] }),
        1 : lambda m: m({ msg.B : state[3] }),
        2 : lambda m: m({ msg.A : state[3] }),
        3 : lambda m: m({ msg.C : state[4] }),
        4 : lambda m: m({ msg.D : state[5] }),
        5 : lambda m: m({ }),
    }
    
    ## how to use it: ######################################
    
    s = StateMachine(state[0])
    s(msg.A)
    assert s.state is state[1]
    
