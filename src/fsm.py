#!/usr/bin/env python
# -*- coding: utf-8 -*-

class FSM(object):

    def __init__(self):
        self.states = {}
        self.currentState = None
        self.transitions = []

    def addState(self, state):
        self.states[state.name] = state

    def deleteState(self, state):
        self.states.pop(state.name)

    def getStateByName(self, stateName):
        return self.states[stateName]

    def addTransition(self, transition):
        if transition.start in self.states and transition.next in self.states:
            self.transitions.append(transition)
            transition.start.addOutTransition(transition)
            transition.next.addInTransition(transition)

    def deleteTransition(self, transition):
        self.transitions.remove(transition)


class State(object):

    def __init__(self, name):
        self.name = name
        self.in_trans = []
        self.out_trans = []

    def addInTransition(self, transition):
        self.in_trans.append(transition)

    def addOutTransition(self, transition):
        self.out_trans.append(transition)


class Transition(object):

    def __init__(self, start, next, guard=None):
        self.start = start
        self.next = next
        self.guard = guard


if __name__ == '__main__':
    import argparse
    import string
    import sys
