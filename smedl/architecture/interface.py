import collections

from .event import Event
from .connectionExpr import ConnectionExpr

class Interface(object):

    def __init__(self,name,pa,ie,ee):
        self.id = name              #string
        self.params = pa            #list of strings
        self.importedEvents = ie    #Event (event.py)
        self.exportedEvents = ee    #Event (event.py)

    def __str__(self):
        out = "mon:"
        if not (self.id == None):
            out+=' name:'+(self.id)
        if not self.params == None:
            out += 'params:'+' '.join(str(s) for s in self.params)
        if not self.importedEvents == None:
            out += ' imported events: '+' '.join(str(s) for s in self.importedEvents)
        if not self.exportedEvents == None:
            out += ' exported  events: '+' '.join(str(s) for s in self.exportedEvents)
        return out
