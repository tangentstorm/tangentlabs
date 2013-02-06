"""
Helpers for building wxPyhon GUIs.
"""
import wx

def menuBar(*menus):
    """
    menus :: [MenuSpec]
    type MenuSpec = (str, wx.Menu)
    """
    assert menus, "no menus passed to menuBar!"
    mb = wx.MenuBar()
    for label,m in menus:
        mb.Append(m, label)
    return mb

def menu(*spec):
    """
    spec :: [MenuArg] where
    data MenuArg
        = label :: str
        | (id::int, label::str)
        | (id::int, label::str, statusText::str)
    """
    m = wx.Menu()
    for item in spec:
        if isinstance(item, str): 
            m.Append(wx.NewId(), item)
        else:
            m.Append(**item)
    return m
