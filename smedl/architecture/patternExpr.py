import collections

class PatternExpr(object):

    def __init__(self):
        self.leftTerm = None
        self.leftIndex = -1
        self.rightTerm = None
        self.rightIndex = -1
        self.operator = None

    def addOperator(self,op):
        if not isinstance(op, str):
            raise TypeError("Invalid type for operator.")
        if not op=="<>" and not op=="=":
            raise TypeError("Invalid operator")
        self.operator = op

    def getOperator(self):
        return self.operator

    def addTerm(self,lt,li,rt,ri):
        if not isinstance(lt,str) or not isinstance(li,int) or not isinstance(rt,str) or not isinstance(ri,int):
            raise TypeError("Invalid type for term or index")
        self.leftTerm = lt
        self.leftIndex = li
        #print(self.leftIndex)
        self.rightTerm = rt
        self.rightIndex = ri

    def getLeftTerm(self):
        return self.leftTerm

    def getRightTerm(self):
        return self.rightTerm

    def getLeftIndex(self):
        return self.leftIndex
    
    def getRightIndex(self):
        return self.rightIndex

    def __str__(self):
        out = "patternExpr:"
        out+=self.getLeftTerm()+'['+str(self.getLeftIndex())+']'+self.operator+self.getRightTerm()+'['+str(self.getRightIndex())+']'
        return out
