
import pygame
from pygame.locals import *

pygame.init()

if pygame.joystick.get_count():
    pad = pygame.joystick.Joystick(0)
    pad.init()
else:
    pad = None
    print "no joystick found"

SCREENSIZE =(50, 50)
    
screen = pygame.display.set_mode(SCREENSIZE)
background = pygame.Surface(screen.get_size())
background = background.convert()
background.fill((250, 0, 250))
screen.blit(background, (0,0))
pygame.display.flip()

while True:
    for event in pygame.event.get():
        if event.type == QUIT:
            break
        else:
            print event

