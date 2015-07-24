#!/usr/bin/env python
# -*- coding: utf-8 -*-

import collections

class FSM(object):

    def __init__(self):
        self.states = collections.OrderedDict()
        self.currentState = None
        self.transitions = []

    def addState(self, state):
        if not isinstance(state, State):
            raise TypeError("Invalid type for state argument.")
        self.states[state.name] = state
        return self.states[state.name]

    def deleteState(self, state):
        if not isinstance(state, State):
            raise TypeError("Invalid type for state argument.")
        self.states.pop(state.name)

    def stateExists(self, stateName):
        if not isinstance(stateName, basestring):
            raise TypeError("Invalid type for name argument.")
        return stateName in self.states

    def getStateByName(self, stateName):
        if not isinstance(stateName, basestring):
            raise TypeError("Invalid type for name argument.")
        return self.states[stateName]

    def addTransition(self, transition):
        if not isinstance(transition, Transition):
            raise TypeError("Invalid type for transition argument.")
        if transition.startState in self.states.values() and transition.nextState in self.states.values():
            self.transitions.append(transition)
            transition.startState.addOutTransition(transition)
            transition.nextState.addInTransition(transition)
        if transition.elseState and transition.elseState in self.states.values():
            transition.elseState.addInTransition(transition)

    def deleteTransition(self, transition):
        self.transitions.remove(transition)

    def getTransitionsByEvent(self, event):
        if not isinstance(event, basestring):
            raise TypeError("Invalid type for event argument.")
        transitions = []
        for t in self.transitions:
            if t.event == event:
                transitions.append(t)
        return transitions

    def __str__(self):
        out = "States:\n\n"
        out += '\n\n'.join(str(s) for s in self.states.values())
        out += "\n\nTransitions:\n"
        out += '\n'.join(("  " + str(t)) for t in self.transitions)
        return out


class State(object):

    def __init__(self, name):
        if not isinstance(name, basestring):
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

    def __init__(self, startState, event, nextState, nextActions=None, guard=None, elseState=None, elseActions=None):
        if not isinstance(startState, State) or \
        not isinstance(event, basestring) or \
        not isinstance(nextState, State) or \
        (nextActions is not None and not isinstance(nextActions, list)) or \
        (guard is not None and not isinstance(guard, basestring)) or \
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
        s = self.startState.name + ' -> ' + self.nextState.name + ' / event: ' + self.event
        if self.guard:
            s = s + ' / if: ' + self.guard
        if self.nextActions:
            s = s + ' / actions: ' + ", ".join(self.nextActions)
        return s

    def str_else(self):
        if not self.elseState:
            return ''
        s = self.startState.name + ' -> ' + self.elseState.name + ' / event: ' + self.event
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


if __name__ == '__main__':
    import argparse
    import string
    import sys
