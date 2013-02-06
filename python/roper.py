import rope.base.project
from rope.refactor import sourceutils

ceo = rope.base.project.Project("c:/svn/ceomatic")


def dump_scope(mod, scope, depth=1):
    obj = scope.pyobject
    lines = mod.lines
    print '%s%s [%s:%s|%s:%s]' % (
        '   ' * depth,
        obj.get_name(), 
        scope.start,
        scope.end, 
        lines.get_line_start(scope.start),
        lines.get_line_end(scope.end))
    for child in scope.get_scopes():
        dump_scope(mod, child, depth+1)

def dump_module(proj, name):
    mod = proj.pycore.get_module(name)
    print "%s:" % name
    for scope in mod.get_scope().get_scopes():
        dump_scope(mod, scope)

dump_module(ceo, "gridliner")
exit()
dump_module(gl)

print dir(gl)
print gl.get_scope().get_scopes()
print dir(gl.scope)







glDir = gl.get_attributes()
names = glDir.keys()
out = glDir['Outline']
print out.get_definition_location()
print out.pyobject.get_name()
print "\n"
outMeths = out.pyobject.get_attributes()
for k,v in sorted(outMeths.items()):
    print k, v.get_definition_location()
print "\n"
wrap = outMeths['wrap']
print dir(wrap.pyobject)

print "\n"
print wrap.pyobject.get_scope()

outScope = out.pyobject.get_scope()
print outScope
print outScope.get_scopes()
print outScope.end

su = sourceutils
print su.get_body_region(wrap.pyobject)
print sourceutils.get_body(wrap.pyobject)











import handy
def dump(scope, depth=0):
    line = "%s%s:" % (obj.get_name, su.get_body_region(obj))
    print handy.indent('#  '*depth, line)
    scope = obj.get_scope()
    
    


for scope in gl.get_scope().get_scopes():
    pyo = scope.pyobject
    dump(pyo)


    print ">>>", pyo.get_type()
    print dir(pyo)
    print 
    print dir(scope)
    break


