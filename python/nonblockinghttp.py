
import socket
import string
import select

from urlparse import urlparse, urlunparse
from httplib import HTTP, HTTP_PORT

from errno import EINPROGRESS, ETIMEDOUT

class localHTTP(HTTP):
	def __init__(self, host = '', port = 0, timeout = 10.0):
		self.connect_timeout = timeout
		HTTP.__init__(self, host, port)
		
	def connect(self, host, port = 0):
		if not port:
			i = string.find(host, ":")
			if i >= 0:
				host, port = host[:i], host[i+1:]
				try:
					port = string.atoi(port)
				except string.atoi_error:
					raise socket.error, "nonnumeric port"
		if not port:
			port = HTTP_PORT
		
		self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
		if self.debuglevel > 0:
			print "connect:", (host, port)
		
		self.sock.setblocking(0)
		try:
			self.sock.connect(host, port)
		except socket.error, why:
			if why[0] == EINPROGRESS:
				pass
			else:
				raise socket.error, why

		(r, w, e) = select.select([], [self.sock], [], self.connect_timeout)
		if w == [self.sock]:
			self.sock.setblocking(1)
			return
		else:
			raise socket.error, (ETIMEDOUT, "timeout during connect phase")

def checkurl(url):
	if url == "" or url == None:
		return None
	
	u = urlparse(url)
	netloc = u[1]
	path = u[2]
	
	h = localHTTP(netloc)
	h.set_debuglevel(0)
	h.putrequest("GET", path)
	h.putheader("accept", "text/html")
	h.putheader("accept", "text/plain")
	h.endheaders()
	
	return h.getreply()

if __name__ == "__main__":
	print checkurl("http://manifestation.com:80/")
	
