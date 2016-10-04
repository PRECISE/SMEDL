#!/usr/bin/env python
# -*- coding: utf-8 -*-

#-------------------------------------------------------------------------------
# state.py
#
# Peter Gebhard (pgeb@seas.upenn.edu)
#
# A basic Finite State Machine class
#-------------------------------------------------------------------------------

class State(object):

    def __init__(self, name):
        if not isinstance(name, str):
            raise TypeError("Invalid type for name argument.")
        self.name = name
        self.in_trans = []
        self.out_trans = []


    def addInTransition(self, transition):
        self.in_trans.append(transition)


    def addOutTransition(self, transition):
        self.out_trans.append(transition)


    def __str__(self):
        s = "State: " + self.name + "\nIn Transitions:\n"
        for trans in self.in_trans:
            if trans.nextState == self:
                s = s + '  ' + trans.str_next() + '\n'
            if trans.elseState == self:
                s = s + '  ' + trans.str_else() + '\n'
        s = s + "\nOut Transitions:\n"
        for trans in self.out_trans:
            s = s + '  ' + trans.str_next() + '\n'
            if trans.elseState:
                s = s + '  ' + trans.str_else() + '\n'
        return s
