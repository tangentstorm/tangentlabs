<?xml version="1.0" encoding="utf-8"?>
<!-- Created by Leo (http://webpages.charter.net/edreamleo/front.html) -->
<?xml-stylesheet ekr_test?>
<leo_file xmlns:leo="http://www.leo-editor.org/2011/leo" >
<leo_header file_format="2" tnodes="0" max_tnode_index="0" clone_windows="0"/>
<globals body_outline_ratio="0.5" body_secondary_ratio="0.5">
	<global_window_position top="50" left="50" height="500" width="700"/>
	<global_log_window_position top="0" left="0" height="0" width="0"/>
</globals>
<preferences/>
<find_panel_settings/>
<vnodes>
<v t="tangentstorm.20130706095433.12222" a="E"><vh>script examples</vh>
<v t="tangentstorm.20130706095433.12208"><vh>@button showFullScreen</vh></v>
<v t="tangentstorm.20130706095433.5625"><vh>@button clone</vh></v>
<v t="tangentstorm.20130706095433.5626"><vh>@button sup?</vh></v>
<v t="tangentstorm.20130706095433.4037"><vh>@button querydocs</vh></v>
</v>
<v t="tangentstorm.20130706095433.12212" a="E"><vh>@path c:/ver/tangentlabs/</vh>
<v t="tangentstorm.20130706095433.12213"><vh>@auto C:/ver/tangentlabs/forth/startingforth-ch1.fs</vh></v>
<v t="tangentstorm.20130706095433.12214"><vh>@auto C:/ver/tangentlabs/python/tornado_ws_wsgi.py</vh></v>
<v t="tangentstorm.20130706095433.12224"><vh>@auto C:/ver/tangentlabs/pascal/tabfile.pas</vh></v>
</v>
</vnodes>
<tnodes>
<t tx="tangentstorm.20130706095433.12208">win = c.frame.top.window()
win.showFullScreen()
win.raise_

# to switch back:
# win.showMaximized()



#g.es('\n'.join(dir(c.frame.top))) </t>
<t tx="tangentstorm.20130706095433.12212"></t>
<t tx="tangentstorm.20130706095433.12222"></t>
<t tx="tangentstorm.20130706095433.4037">@language python

rpt = p.insertAsLastChild()
rpt.h = 'report'

obj = c.frame
for member in dir(obj):
    if member.find('') &gt; -1:
        docstring = getattr(obj, member).__doc__
        node = rpt.insertAsLastChild()
        node.h = member
        node.b = docstring

c.redraw()</t>
<t tx="tangentstorm.20130706095433.5625">p.clone()
c.redraw()
</t>
<t tx="tangentstorm.20130706095433.5626">p.createFirstChildNode('sup baby?')
c.redraw()
</t>
</tnodes>
</leo_file>
