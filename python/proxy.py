
class Proxy(object):

   def __init__(self, obj, path=''):
      self.__dict__['obj'] = obj
      self.__dict__['path']= path

   def __getitem__(self, name):
       return Proxy(obj=self.obj[name],
                    path="{p}[{n}]".format(p=self.path, n=name))
    
   def __setitem__(self, name, value):
       print "LOG: {p}[{n}]={v}".format(p=self.path, n=name, v=value)
       self.__dict__['obj'][name] = value
    
   def __getattr__(self, name):
       return Proxy(obj=self.obj[name],
                    path="{p}.{n}".format(p=self.path, n=name))
    
   def __setattr__(self, name, value):
       print "LOG: {p}.{n}={v}".format(p=self.path, n=name, v=value)
       setattr(self.__dict__['obj'], name, value)


class Thing(dict):
    pass

p = Proxy(Thing(), 'p')
p['x']={'y':{'z':0}}
p['x']['y']['z'] = 7
p.a = 'b'
