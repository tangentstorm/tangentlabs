background = pygame.image.load("data/stars.bmp")
pygame.transform.scale(background, (1200,800))  #or some size x,y here.
bgRect = background.get_rect()
size = width, height = bgRect.width, bgRect.height
screen = pygame.display.set_mode(size)
screen.blit(background, bgRect)
pygame.display.flip()
