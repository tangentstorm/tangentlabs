import wx, wxchrome
win = wx.Frame(None, -1, "ChromeTab")
chrome = wxchrome.ChromeFrameWindow(win)
chrome.load_url("http://google.com/")
win.Show()
