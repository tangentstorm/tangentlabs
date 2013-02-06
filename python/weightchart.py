# third weight charting program
# 1210.2000 by michal wallace

from graphite import *

def addLegend(g, colors, names, x=0.1, y=0.8):
	"add a legend, using colors only (no symbols or line styles)"
	for i in range(len(names)):
		color = colors[i%len(colors)]
		# add the box
		g.overlays.append( Box((x,y,0),(x+0.04,y+0.06,0),fillStyle=color) )
		# add the text
		g.overlays.append( Text(names[i],pos=(x+0.06,y+0.03,0),
				style=TextStyle(hjust=LEFT,vjust=CENTER,font=Font(size=10))) )
		# move to text item
                y = y - 0.08



g = Graph()

# append some data, and set the line styles
goal = Dataset((1,236), (84,200)) # goal is to lose 36lbs and reach 200
actual = Dataset(
    ( 1, 235.6), # 1209.2000 BODYFAT: 25.0%
                 # (got a new scale with digital precision)
    ( 2, 234.6), # 1210.2000
    ( 3, 234.6), # 1211.2000
    ( 4, 235.2), # 1212.2000
    #
    ( 6, 237.6), # 1214.2000
    #
    ( 9, 236),   # 1217.2000
    #
    (11, 237.2), # 1219.2000
    #(18,228), # graphite seems to ignore the last point for some reason..
    )

g.datasets.append(goal)
#g.datasets.append(revised)
g.datasets.append(actual)

blueplot = PointPlot()
blueplot.lineStyle.color = blue
blueplot.lineStyle.width = 1
blueplot.lineStyle.kind = SOLID
blueplot.symbol = None

import copy
greenplot = copy.deepcopy(blueplot)
greenplot.lineStyle.color = green

blackplot = copy.deepcopy(blueplot)
blackplot.lineStyle.color = black

g.axes[Y].label.text = "Weight"
g.axes[X].label.text = "Time"
g.formats = [greenplot, blackplot]


colors = [green, black]
names = ["goal", "actual"]

addLegend(g,colors,names, y=.25)
genOutput(g, "PIL", size=(400,250), canvasname="weight03.gif")

