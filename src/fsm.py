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

    def __str__(self):
        for s in states:
            print(s)


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
        print("State: " + self.name)
        print("In Transitions: ")
        for i in self.in_trans:
            print("  " + str(i))
        print("Out Transitions: ")
        for o in self.out_trans:
            print("  " + str(o))



class Transition(object):

    def __init__(self, start, next, guard=None):
        if not isinstance(start, State) or not isinstance(next, State) or not isinstance(guard, str):
            raise TypeError("Invalid argument type(s).")
        self.start = start
        self.next = next
        self.guard = guard

    def __str__(self):
        print(self.start.name + " -> " + self.next.name + " / guard: " + self.guard)


if __name__ == '__main__':
    import argparse
    import string
    import sys
