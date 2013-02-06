
from cogen.web import wsgi
from cogen.common import *

def my_crazy_app(environ, start_response):
    status = '200 OK'
    response_headers = [('Content-type','text/plain')]
    start_response(status, response_headers)
    return ["Lorem ipsum dolor sit amet, consectetuer adipiscing elit."]


sched = Scheduler(default_priority=priority.LAST, default_timeout=15)
server = wsgi.WSGIServer(
            ('localhost', 8070), 
            my_crazy_app,
            sched,
            server_name='localhost')
sched.add(server.serve)
try:
    sched.run()
except (KeyboardInterrupt, SystemExit):
    pass
