#! /usr/bin/env python

import pygame
import sys

def quit():
    sdl.quit()
    sys.exit(0)

def do_activeevent(event):
    gain = event.get_gain()
    state = event.get_state()
    print "Event type: ACTIVEEVENT"
    if gain == 0: print "Gain = 0 (lost)"
    else: print "Gain = 1 (gained)"
    if state == 0: print "State = 0"
    elif state == 1: print "State = 1 APPMOUSEFOCUS"
    elif state == 2: print "State = 2 APPINPUTFOCUS"
    elif state == 4: print "State = 4 APPACTIVE"
    return()

def do_keydown(event):
    mod = event.get_mod()
    state = event.get_state()
    sym = event.get_sym()
    print "Event type: KEYDOWN"
    print "Modifier value: " + str(mod)
    if state == 1:
        print "State: " +str(state) + " - PRESSED"
    else:
        print "State: " + str(state) + "ERROR"
    print "Keysym: " + sdl.events_get_key_name(sym)
    return()

def do_keyup(event):
    mod = event.get_mod()
    state = event.get_state()
    sym = event.get_sym()
    print "Event type: KEYUP"
    print "Modifier value: " + str(mod)
    if state == 0:
        print "State: " +str(state) + " - RELEASED"
    else:
        print "State: " + str(state) + "ERROR"
    print "Keysym: " + sdl.events_get_key_name(sym)
    return()

def do_mousemotion(event):
    state = event.get_state()
    (x, y, x_rel, y_rel) = event.get_coords()
    print "Event type: MOUSEMOTION"
    print "X: " + str(x) + " Y: " + str(y) + " x_rel: " + str(x_rel) + " y_rel: " + str(y_rel)
    print "State: " + str(state)
    return()

def do_mousebuttondown(event):
    print "Event type: MOUSEBUTTONDOWN"
    button = event.get_button()
    (x, y) = event.get_coords()
    state = event.get_state()
    print "Button: " + str(button)
    print "X: " + str(x) + ", Y: " + str(y)
    if state == 1:
        print "State: " +str(state) + " - PRESSED"
    else:
        print "State: " + str(state) + "ERROR"
    return()

def do_mousebuttonup(event):
    print "Event type: MOUSEBUTTONUP"
    button = event.get_button()
    (x, y) = event.get_coords()
    state = event.get_state()
    print "Button: " + str(button)
    print "X: " + str(x) + ", Y: " + str(y)
    if state == 0:
        print "State: " +str(state) + " - RELEASED"
    else:
        print "State: " + str(state) + "ERROR"
    return()

def do_joyaxismotion(event):
    print "Event type: JOYAXISMOTION"
    state = event.get_state()
    (id, axis) = event.get_ids()
    print "State: " + str(state)
    print "ID: " + str(id) + ", Axis: " + str(axis)
    return()

def do_joyballmotion(event):
    print "NOT YET IMPLEMENTED."
    return()

def do_joyhatmotion(event):
    print "Event type: JOYHATMOTION"
    (joy_id, hat_id) = event.get_ids()
    pos = event.get_pos()
    print "Joystick: " + str(joy_id) + ", Hat: " + str(hat_id)
    print "Position: " + str(pos)
    return()

def do_joybuttonup(event):
    (joy_id, button) = event.get_ids()
    state = event.get_state()
    print "Joystick: " + str(joy_id) + ", Button: " + str(button)
    if state == 0:
        print "State: " +str(state) + " - RELEASED"
    else:
        print "State: " + str(state) + "ERROR"
    return()

def do_joybuttondown(event):
    (joy_id, button) = event.get_ids()
    state = event.get_state()
    print "Joystick: " + str(joy_id) + ", Button: " + str(button)
    if state == 1:
        print "State: " +str(state) + " - PRESSED"
    else:
        print "State: " + str(state) + "ERROR"
    return()

def do_quit(event):
    print "Event type: QUIT"
    quit()

def do_userevent(event):
    print "Event type: USEREVENT - Shouldn't happen."
    return()

def do_unknown(event):
    print "Event type: unknown - Shouldn't happen."
    return()

def handle(event, etype):
    if etype == sdl.ACTIVEEVENT:
        do_activeevent(event)
    elif etype == sdl.KEYDOWN:
        do_keydown(event)
    elif etype == sdl.KEYUP:
        do_keyup(event)
    elif etype == sdl.MOUSEMOTION:
        do_mousemotion(event)
    elif etype == sdl.MOUSEBUTTONDOWN:
        do_mousebuttondown(event)
    elif etype == sdl.MOUSEBUTTONUP:
        do_mousebuttonup(event)
    elif etype == sdl.JOYAXISMOTION:
        do_joyaxismotion(event)
    elif etype == sdl.JOYBALLMOTION:
        do_joyballmotion(event)
    elif etype == sdl.JOYHATMOTION:
        do_joyhatmotion(event)
    elif etype == sdl.JOYBUTTONDOWN:
        do_joybuttondown(event)
    elif etype == sdl.JOYBUTTONUP:
        do_joybuttonup(event)
    elif etype == sdl.QUIT:
        do_quit(event)
    elif etype == sdl.USEREVENT:
        do_userevent(event)
    else:
        do_unknown(event)
    return(1)

width = 200
height = 200
depth = 16

# main

pygame.init()
pygame.display.set_mode((150,50))
#pygame.init(pygame.INIT_JOYSTICK)

while True:
    e = pygame.event.wait()
    if e.type == pygame.QUIT:
        break
    print e


#display = sdl.video_set_mode(width, height, depth, sdl.SWSURFACE)
#if sdl.joy_get_count() > 0:
#    joy = sdl.joy_open(0)
#
#while 1:
#    event = sdl.events_wait()
#    handle(event, event.get_type())
#    print "-----------------------------------------------"
    


