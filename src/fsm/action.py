#!/usr/bin/env python
# -*- coding: utf-8 -*-

#-------------------------------------------------------------------------------
# action.py
#
# Peter Gebhard (pgeb@seas.upenn.edu)
#
# A basic Finite State Machine class
#-------------------------------------------------------------------------------

import collections
from enum import Enum
from parser.astToPython import AstToPython

class Action(object):

    def __init__(self):
        self.type = ActionType.Undefined


class ActionType(Enum):
    StateUpdate = 1
    Raise = 2
    Instantiation = 3
    Call = 4
    Undefined = 5


class StateUpdateAction(Action):

    def __init__(self, target, operator, expression=None):
        super(StateUpdateAction, self).__init__()
        self.type = ActionType.StateUpdate
        self.target = target
        self.operator = operator
        self.expression = expression


    def __str__(self):
        out = "ActionType: State Update; Target: " + self.target + "; Operator: " + self.operator
        if self.expression:
            out += "; Expression: " + str(self.expression)
        return out


class RaiseAction(Action):

    def __init__(self, event, params):
        super(RaiseAction, self).__init__()
        self.type = ActionType.Raise
        self.event = event
        self.params = params


    def __str__(self):
        out = "ActionType: Raise; Event raised: " + self.event + "; Event parameters : "
        out += ', '.join(t for t in self.params)
        return out


class InstantiationAction(Action):

    def __init__(self, object, params):
        super(InstantiationAction, self).__init__()
        self.type = ActionType.Instantiation
        self.object = object
        self.params = params


    def __str__(self):
        out = "ActionType: Instantiation; Object instantiated: " + self.object + "; Object instantiation parameters : "
        out += ', '.join(t for t in self.params)
        return out


class CallAction(Action):

    def __init__(self, target, params):
        super(CallAction, self).__init__()
        self.type = ActionType.Call
        self.target = target
        self.params = AstToPython.expr_list(params)
        print("Call: " + str(self.target) + "   " + str(self.params))


    def __str__(self):
        out = "ActionType: Call; Call target: " + self.target + "; Call parameters : "
        out += ', '.join(t for t in self.params)
        return out
