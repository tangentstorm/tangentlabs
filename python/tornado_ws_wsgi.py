"""
This demonstrates how to mix WSGI and WebSockets in Tornado
"""
import tornado.web
import tornado.httpserver
import tornado.ioloop
import tornado.websocket as ws
import tornado.wsgi


kHOST = 'localhost'
kPORT = '8888'

class EchoWebSocket(ws.WebSocketHandler):
    """
    A demo web socket server from:

    http://www.tornadoweb.org/documentation/websocket.html
    """
    def open(self):
        print "WebSocket opened"

    def on_message(self, message):
        self.write_message(u"You said: " + message)

    def on_close(self):
        print "WebSocket closed"


def echo_test_wsgi(env, start):
    """
    A simple wsgi application that embeds the js side of the websocket demo from:

        http://www.tornadoweb.org/documentation/websocket.html

    """
    status = "200 OK"
    response_headers = [("Content-type", "text/html")]
    start(status, response_headers)

    js = """
    <html>
    <head>
      <meta http-equiv="Content-Type" content="text/html; charset=utf-8"/>
      <script type="text/javascript">
        var ws = new WebSocket("ws://%s/ws/echo");
        ws.onopen = function() {
            ws.send("Hello, world!");
        };
        ws.onmessage = function (evt) {
            alert(evt.data);
        };
      </script>
    </head>
    <body>
      <p>If all goes well, you should see a popup that says "You said: Hello, world!"</p>
    </body>
    </html>
    """ % (env['HTTP_HOST']) #  env['SERVER_PORT'])

    return js


def main():
    """
    Builds and runs the server, with the websocket handler and
    and the wsgi application running side by side.
    """
    app = tornado.web.Application([
        (r'/ws/echo', EchoWebSocket),

        # note that you need both the FallBackHandler and the WSGIContainer
        (r'.*', tornado.web.FallbackHandler, {
            'fallback': tornado.wsgi.WSGIContainer(echo_test_wsgi) }),
    ])
    server = tornado.httpserver.HTTPServer(app)
    server.listen(port=kPORT, address=kHOST)

    print("starting server at http://{0}:{1}/".format(kHOST, kPORT))
    tornado.ioloop.IOLoop.instance().start()

if __name__=="__main__":
    main()

