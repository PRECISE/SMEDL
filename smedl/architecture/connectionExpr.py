import collections

from .patternExpr import PatternExpr

class ConnectionExpr(object):

    def __init__(self,cn,sm,se,tm,te,ps):
        self.connName = cn
        self.sourceMachine = sm
        self.sourceEvent = se
        self.targetMachine = tm
        self.targetEvent = te
        self.patternSpec = ps

    def __str__(self):
        out = "connectionExpr:"
        if not self.connName == None:
            out+=' connName:'+self.connName
        if not self.sourceMachine == None:
            out+=' sourceMachine:'+self.sourceMachine
        if not self.sourceEvent == None:
            out+=' sourceEvent:'+self.sourceEvent
        if not self.targetMachine == None:
            out+=' targetMachine:'+self.targetMachine
        if not self.targetEvent == None:
            out+=' targetEvent:'+self.targetEvent
        if not self.patternSpec == None:
            out+=' patternSpec:'+' '.join(str(s) for s in self.patternSpec)
        return out


