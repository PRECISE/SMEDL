#!/usr/bin/env python
# -*- coding: utf-8 -*-

class FSM(object):

    def __init__(self):
        self.states = {}
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
        if not isinstance(stateName, str):
            raise TypeError("Invalid type for name argument.")
        return stateName in self.states

    def getStateByName(self, stateName):
        if not isinstance(stateName, str):
            raise TypeError("Invalid type for name argument.")
        return self.states[stateName]

    def addTransition(self, transition):
        if not isinstance(transition, Transition):
            raise TypeError("Invalid type for transition argument.")
        if transition.start in self.states and transition.next in self.states:
            self.transitions.append(transition)
            transition.start.addOutTransition(transition)
            transition.next.addInTransition(transition)

    def deleteTransition(self, transition):
        self.transitions.remove(transition)

    def __str__(self):
        return '\n'.join(str(s) for s in self.states)


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
        s = "State: " + self.name + '\n' + "In Transitions: " + '\n'
        s = s + "\n".join(("  " + str(i)) for i in self.in_trans)
        s = s + "Out Transitions: " + '\n'
        s = s + "\n".join(("  " + str(i)) for i in self.out_trans)
        return s


class Transition(object):

    def __init__(self, start, next, guard=None):
        if not isinstance(start, State) or not isinstance(next, State) or (guard is not None and not isinstance(guard, str)):
            raise TypeError("Invalid argument type(s).")
        self.start = start
        self.next = next
        self.guard = guard

    def __str__(self):
        return self.start.name + " -> " + self.next.name + " / guard: " + self.guard


if __name__ == '__main__':
    import argparse
    import string
    import sys
