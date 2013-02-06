if True:
    import pyglet, random

    window = pyglet.window.Window()

    label = pyglet.text.Label('Hello, world',
                              font_name='Times New Roman',
                              font_size=36,
                              x=window.width//2, y=window.height//2,
                              anchor_x='center', anchor_y='center')
    @window.event
    def on_draw():
        window.clear()
        label.draw()

    @window.event
    def on_key_press(symbol, modifiers):
        pyglet.image.get_buffer_manager().get_color_buffer().save('screenshot.png')

    def update(dt):
        label.x += random.randint(-10, 10)
        label.y += random.randint(-10, 10)

    pyglet.clock.schedule_interval(update, 0.1)
    pyglet.app.run()

