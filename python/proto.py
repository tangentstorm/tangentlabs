#!/usr/bin/python2.2
#
# openEEG software prototype
# by michal wallace (sabren@manifestation.com)
#
# python prototype of a mind-mirror style biofeedback machine
# Basically, this is just a spectral analysis program.
#
# This version still only graphs fake data, but adds windowing
# to clean up some of the noise. The scale is still wrong, though. 
#
# $Id: proto.py,v 1.4 2002/06/15 23:22:21 sabren Exp $

## dependencies: #####################################################

try:
    import Numeric                      # http://www.pfdubois.com/numpy/
    import MLab, FFT, RandomArray       # (parts of numeric)
    import pygame                       # http://www.pygame.org/
    from pygame.locals import *
except:
    raise SystemExit, "This program requries NumPy and pygame."

# the rest of these come with python:
import whrandom
import time

## graphic routines ##################################################

def makeGradient():
    """
    Returns an 163*10 Surface showing mirrored green-yellow-red
    gradients with a blue line in between.
    """
    colors = []
    for i in range(0, 0xff, 0x22):
        colors.append((i, 0xff, 0))
    colors.append((0xff, 0xff, 0))
    for i in range(0xcc, -1, -0x22):
        colors.append((0xff, i, 0))

    rcolors = colors
    lcolors = colors[:]; lcolors.reverse()

    center = 80

    sprite = pygame.Surface((163, 10))
    for x in range(len(colors)):
        # left (red to green)
        pygame.draw.rect(sprite, lcolors[x],
                         pygame.Rect(x*5, 1, 4, 8))
        
        # right (green to red)
        pygame.draw.rect(sprite, rcolors[x],
                         pygame.Rect(center+2+(x*5), 1, 4, 8))

    pygame.draw.line(sprite, (0xcc,0xcc,0xff), (center, 0), (center, 10))
    return sprite


def makeWindow(winsize):
    pygame.init()
    pygame.display.set_caption("openEEG prototype")
    return pygame.display.set_mode(winsize, RESIZABLE, 0)


def keepLooping():
    pygame.display.update()
    for e in pygame.event.get():
        if (e.type == KEYUP and e.key == K_ESCAPE) \
        or (e.type == QUIT):
            return 0
    return 1



## data routines #####################################################

def wave(frequency, sampRate=256.0):
    """
    Returns a sampled wave at the given frequency and sample rate.

    This routine is generalized from Eric Hagemann's article at:
    http://www.onlamp.com/pub/a/python/2001/01/31/numerically.html
    """
    return Numeric.sin(2 * Numeric.pi
                         * (frequency/sampRate)
                         * Numeric.arange(sampRate))


def fakeSession():
    """
    Creates ten seconds of completely fake data.
    """
    pureAlpha = 10                      # alpha is 8-12hz
    pureBeta  = 20                      # beta is 13-30hz
    pureTheta = 6                       # theta is 4-8hz
    pureDelta = 2                       # delta is 0.5-4hz

    sec = [None] * 10                   # make an empty list
    
    # when animated, this should move right up the line:
    sec[0] = wave(pureDelta)
    sec[1] = wave(pureTheta)
    sec[2] = wave(pureAlpha)
    sec[3] = wave(pureBeta)

    # and this should move back down in pairs:
    sec[4] = wave(pureBeta)  + wave(pureAlpha)
    sec[5] = wave(pureAlpha) + wave(pureTheta)
    sec[6] = wave(pureTheta) + wave(pureDelta)
    sec[7] = wave(pureDelta) + wave(pureBeta)

    # all four at once:
    sec[8] = wave(pureDelta) + wave(pureTheta) \
             + wave(pureAlpha) + wave(pureBeta)

    # and then silence:
    sec[9] = wave(0)

    return Numeric.concatenate(sec)


def makeSpectrogram(slice):
    """
    Returns a list of length 32, with the FFT of the slice.
    We seem to need 64 samples to do this.
    If the sample rate is 256Hz, then we're talking about
    1/4th of a second's worth of data here.
    """
    assert len(slice)==64, "we want 32 bins, so we need 64 samples"

    res = abs(FFT.real_fft(slice))[:-1] # discard 33rd slot (is this okay?)
    res = Numeric.floor(res) # round off to integers
    
    assert len(res)==32, len(res)    
    return res
    

## main program ######################################################

def main():
    #@TODO: make names for all these magic numbers...
    
    screen = makeWindow(winsize=(200, 400))
    grad = makeGradient()
    
    black = pygame.Surface((80,10))
    black.fill((0,0,0))

    # the windowing array quiets down the edges of the sample
    # to prevent "clicking" at the edges:
    windowing = MLab.blackman(64)
    
    session = fakeSession()
    t = 0
    
    center= 81 # same as in creating the graph @TODO: consolidate these

    while keepLooping():

        # simulate aquiring data for 1/4th of a second (64 samples):
        time.sleep(0.25) 

        data = session[t:t+64] * windowing
        graph = makeSpectrogram(data)

        t += 64
        if t >= len(session):
            t = 0

        # draw the gradient, then cover part of it up:
        for i in range(32):
            screen.blit(grad, (20,         20+i*10))
            # left is blank for now:
            #screen.blit(black,(20 +(0       ), 20+i*10))
            # right side shows the data:
            screen.blit(black,(20+center+(graph[i]*10), 20+i*10))


if __name__=="__main__":
    main()
