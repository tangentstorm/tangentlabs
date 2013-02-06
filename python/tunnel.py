
from twisted.internet.protocol import Protocol, Factory, ClientFactory
from twisted.internet import reactor
from twisted.protocols import basic
from sys import stdout

class FarSide(Protocol):
    def __init__(self, callback):
        self.callback = callback
    def dataReceived(self, data):
        self.callback(data)
    def sendData(self, data):
        self.transport.write(data)
        
class FarFactory(ClientFactory):
    protocol = FarSide
    def __init__(self, nearside):
        self.nearside = nearside
    def buildProtocol(self, addr):
        self.nearside.farSide = FarSide(self.nearside.onResponse)
        return self.nearside.farSide

class NearSide(Protocol):
    def __init__(self, farHost, farPort):
        self.farHost = farHost
        self.farPort = farPort

    def connectionMade(self):
        farFact = FarFactory(self)
        reactor.connectTCP(self.farHost, self.farPort, farFact)

    def onResponse(self, data):
        # from farside to nearside
        print "s>", data
        # and nearside to client:
        self.transport.write(data)
        
    def dataReceived(self, data):
        # from client to nearside
        print "n>", data
        # and nearside to farside
        self.farSide.sendData(data)

class NearFactory(Factory):
    def __init__(self, farHost, farPort):
        self.farHost = farHost
        self.farPort = farPort
    def buildProtocol(self, addr):
        return NearSide(self.farHost, self.farPort)


#@TODO: connectionLost / self.transport.loseConnection

nearFact = NearFactory('google.com', 80)
reactor.listenTCP(9090, nearFact)
reactor.run()

# LineReceiver is protocol with setRawMode / rawDataReceived()
