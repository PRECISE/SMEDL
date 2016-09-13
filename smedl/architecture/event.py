import collections

class Event(object):

    def __init__(self,er,id,pa):
        self.error = er
        self.event_id = id
        self.params = pa

    def __str__(self):
        out = ""
        if not self.error == None:
            out+=self.error+';'
        if not self.event_id == None:
            out+='event_id:' + (self.event_id)
        if not self.params == None:
            out += ' params:'+' '.join(str(s) for s in self.params)+';'
        return out