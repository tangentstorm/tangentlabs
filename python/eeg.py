# python2.7
#
# openEEG software prototype for neurosky mindset
# by michal wallace

## dependencies: #####################################################

import numpy
from numpy import fft
from pygame2.sdl import video, event
from pygame2.sdlext import draw
from pygame2 import Rect, Color
from pygame2.sdl import constants as K
import thinkgear


def makeWindow(winsize):
    win = video.set_mode(winsize)
    # pygame.display.set_caption("openEEG prototype")
    return win


def keepLooping():
    for e in event.get():
        if (e.type == K.KEYUP and e.key == K.K_ESCAPE) \
        or (e.type == K.QUIT):
            return False
    return True


## main program ######################################################

def main():
    #@TODO: make names for all these magic numbers...

    video.init()


    colors = [
        Color(0xff, 0x00, 0x00), # red
        Color(0xff, 0x66, 0x00), # orange
        Color(0xff, 0xff, 0x00), # yellow
        Color(0x00, 0xff, 0x00), # green
        Color(0x00, 0xff, 0xff), # cyan
        Color(0x66, 0x66, 0xff), # blue
        Color(0x99, 0x00, 0x99), # indigo
        Color(0xff, 0x00, 0xff), # violet
        ]
    
        
    maxPower = 500000.0 #(16777215 * 1.0) / 2
    
    eegProtocol = thinkgear.ThinkGearProtocol("com3")
    eeg = eegProtocol.get_packets()
    
    screen = makeWindow(winsize=(640, 480))
    grad = makeGradient()


    chart = video.Surface(480, 100)
    chart.fill(Color(0,0,0))

    value = 0
    center = 50

    maxRaw = 150.0 # only loking for REALLY low power signals
    minRaw = -maxRaw

    while keepLooping():

        packs = eeg.next()
        for d in packs:

            if isinstance(d, thinkgear.ThinkGearRawWaveData):
                # shift one pixel over:
                chart.scroll(-1, 0)
                lastValue = value
                value = int(48.0 * max(minRaw, min(d.value, maxRaw)) / maxRaw)
                draw.line(chart, Color(0xff,0xff,0xff),
                         477, center+lastValue, 478, center+value)

            elif isinstance(d, thinkgear.ThinkGearEEGPowerData):
                data = d.value
                screen.fill(Color(0,0,0))
                for i, v in enumerate(data):
                    x = 100 + (i * 45)
                    w = 40
                    h = max(2, int(340.0 * min(v, maxPower) / maxPower))
                    y = 400 - h
                    draw.rect(screen, colors[i], Rect(x, y, w, h))
            else:
                break
        else: # no break

            # redraw the screen:            
            screen.blit(chart, Rect(50, 200, 0, 0))
            screen.flip()

        pass # end of while
    eegProtocol.io.close()


if __name__=="__main__":
    main()
