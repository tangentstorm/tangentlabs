    #!/usr/bin/python
    import wx
    import wx.grid

    class GridAndMenuFrame(wx.Frame):
        def __init__(self, parent, id, title):
            wx.Frame.__init__(self, parent, id, title, 
                              wx.DefaultPosition, wx.Size(200, 150))

            mbar = wx.MenuBar()
            menu = wx.Menu()
            menu.Append(101, 'E&xit', 'Exit')
            mbar.Append(menu, '&File')
            self.SetMenuBar(mbar)

            grid = wx.grid.Grid(self, -1)
            # obviously, size and configure the grid here


    if __name__ == '__main__':
        app = wx.App(redirect=False)
        win = GridAndMenuFrame(None, -1, "grid and menu")
        win.Show()
        app.MainLoop()
