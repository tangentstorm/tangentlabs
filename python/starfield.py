
import sdl
import time
import random
import math

sdl.init(sdl.INIT_VIDEO)

random.seed(int(time.time()))

w = 640
h = 480
cx = w / 2
cy = h / 2

stars = []

VEL = 0
POS = 1
X = 0
Y = 1

for i in range(120):
    # c[0] is a list containing the star's velocity in [0] x and [1] y
    # c[1] is a list containing the position of the star [0] x and [1] y
    c = ([math.sin(random.random()) * 5, math.sin(random.random()) * 5], [cx , cy])
    stars.append(c)

state = 0

#surface = sdl.video_set_mode(w, h, 0, sdl.SWSURFACE)
surface = sdl.video_set_mode(w, h, 0, sdl.FULLSCREEN)


white = surface.map_rgb((255, 255, 255))
black = surface.map_rgb((0, 0, 0))




while state != -1:
    e = sdl.events_poll()
    if e != -1:
        if e.get_type() == sdl.QUIT or e.get_type() == sdl.KEYDOWN:
            state = -1
            continue
        
    for star in stars:
        surface.set_at(star[POS][X], star[POS][Y], black)
        star[POS][X] = star[POS][X] + star[VEL][X]
        star[POS][Y] = star[POS][Y] + star[VEL][Y]

        if (not (0 < star[POS][X] < w)) \
        or (not (0 < star[POS][Y] < h)):
            star[POS][X] = cx
            star[POS][Y] = cy
            star[VEL][X] = math.sin((random.random()*7)-3) * 5
            star[VEL][Y] = math.sin((random.random()*7)-3) * 5

        surface.set_at(star[POS][X], star[POS][Y], white)

    surface.update_rect((0,0,w,h))


sdl.quit()
