
import ImageGrab # from PIL

#2() + 5 = 77 # trying to trigger error in flymake

img = ImageGrab.grab()
img.save(open("c:/temp/clip.png", "wb"), "PNG")
