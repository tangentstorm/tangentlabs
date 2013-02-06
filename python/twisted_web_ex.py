from twisted.internet import reactor
from twisted.web import server, static, resource


class Saluter(resource.Resource):
    isLeaf = False

    def render(self, request):
        return "<h2>SALUTE</h2>"


if __name__ == '__main__':
    root = static.File(".") # serves any file from current dir
    root.putChild('salute', Saluter())

    site = server.Site(root)
    reactor.listenTCP(8000, site)
    
    reactor.run()
