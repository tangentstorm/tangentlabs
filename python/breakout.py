"""
SmashOut! example game
"""
import os
import pygame

def startPyGame((w, h), title):
    pygame.init()
    pygame.display.set_caption(title)
    screen = pygame.display.set_mode((w, h))
    return screen

def getSprite(path):
    pygame.image.load(os.path.join('data', 'soccer.png'))

# * put something on the screen
"""
Our first trick is to draw a ball:
"""
def main():
    screen = startPyGame((320,200), 'SmashOut!')
    done = False
    while not done:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                done = True
        
if __name__=="__main__":
    main()

    
