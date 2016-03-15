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


class Transition(object):

    def __init__(self, startState, event, nextState, nextActions=None,
            guard=None, elseState=None, elseActions=None):
        if not isinstance(startState, State) or \
            not isinstance(event, str) or \
            not isinstance(nextState, State) or \
            (nextActions is not None and not isinstance(nextActions, list)) or \
            (guard is not None and not isinstance(guard, str)) or \
            (elseState is not None and not isinstance(elseState, State)) or \
            (elseActions is not None and not isinstance(elseActions, list)):
                raise TypeError("Invalid argument type(s).")
        self.startState = startState
        self.event = event
        self.nextState = nextState
        self.nextActions = nextActions
        self.guard = guard
        self.elseState = elseState
        self.elseActions = elseActions


    def str_next(self):
        s = self.startState.name + ' -> ' + self.nextState.name + \
            ' / event: ' + self.event
        if self.guard:
            s = s + ' / if: ' + self.guard
        if self.nextActions:
            s = s + ' / actions: ' + ", ".join(self.nextActions)
        return s


    def str_else(self):
        if not self.elseState:
            return ''
        s = self.startState.name + ' -> ' + self.elseState.name + \
            ' / event: ' + self.event
        if self.guard:
            s = s + ' / if not: ' + self.guard
        if self.elseActions:
            s = s + ' / actions: ' + ", ".join(self.elseActions)
        return s


    def __str__(self):
        s = self.startState.name + ' -> ' + self.event
        if self.guard:
            s = s + ' when ' + self.guard
        if self.nextActions:
            s = s + ' {' + ', '.join(self.nextActions) + '}'
        s = s + ' -> ' + self.nextState.name
        if self.elseState:
            s = s + '\n    else'
            if self.elseActions:
                s = s + ' {' + ', '.join(self.elseActions) + '}'
            s = s + ' -> ' + self.elseState.name
        return s
