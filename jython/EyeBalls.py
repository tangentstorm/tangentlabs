# just a test of JPython

from java.applet import Applet
from java import awt

parent = java.awt.Frame
#parent = Applet

# eyeball thingy
class EyeBalls(parent):
	x = xstart = 80; xwidth = 20
	oscdist = 20; osc = 1;
	def paint(self,g):
		# blue background
		g.setColor(awt.Color.blue)
		g.fillRect(0,0, 200, 200)

		# white eyeballs
		g.setColor(awt.Color.white)
		g.fillOval( 80, 75, 30, 50)
		g.fillOval(100, 75, 30, 50)

		# black pupils
		g.setColor(awt.Color.black)
		g.fillOval( self.x, 105, 10, 10)
		g.fillOval( self.x + self.xwidth, 105, 10, 10)

		# look back and forth:
		self.osc = self.osc + 1
		if self.osc % (self.oscdist * 2) >= self.oscdist:
			self.x = self.x - 1
		else:
			self.x = self.x + 1
		self.repaint()

	def update(self, g):
		g.setClip(self.xstart - 20, 105, \
				  self.xstart + (self.oscdist * 2) + self.xwidth + 10, 110)
		self.paint(g)

if parent != Applet:
	# make a new window
	win = EyeBalls("Eyes!")
	win.setSize(200,200)
	win.visible = 1
