import sdl, sys

sdl.init(sdl.INIT_JOYSTICK + sdl.INIT_VIDEO)

count = sdl.joy_get_count()
if count == 0:
    print "No joysticks detected."
    sys.exit(1)
for id in range(0, count):
    print "Joystick " + str(id) + " : " + sdl.joy_get_name(id)



def handle(event, extra):
    print event, extra

joy = sdl.joy_open(0)
while 1:
    event = sdl.events_wait()
    handle(event, event.get_type())
    print "-----------------------------------------------"    
