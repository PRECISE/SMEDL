#!/usr/bin/env python
# -*- coding: utf-8 -*-

#-------------------------------------------------------------------------------
# fsm.py
#
# Peter Gebhard (pgeb@seas.upenn.edu)
#
# A basic Finite State Machine class
#-------------------------------------------------------------------------------

import collections
from .state import State
from .transition import Transition

class FSM(object):

    def __init__(self):
        self.states = collections.OrderedDict()
        self.startState = None
        self.endState = None
        self.currentState = None
        self.transitions = []
        self.finalstates = []


    def addFinalState(self, state):
        self.finalstates.append(state)
    
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
        if transition.startState in list(self.states.values()) and \
                transition.nextState in list(self.states.values()):
            self.transitions.append(transition)
            transition.startState.addOutTransition(transition)
            transition.nextState.addInTransition(transition)
        if transition.elseState and \
                transition.elseState in list(self.states.values()):
            transition.elseState.addInTransition(transition)


    def deleteTransition(self, transition):
        if not isinstance(transition, Transition):
            raise TypeError("Invalid type for transition argument.")
        self.transitions.remove(transition)


    def getTransitionsByEvent(self, event):
        if not isinstance(event, str):
            raise TypeError("Invalid type for event argument.")
        transitions = []
        for t in self.transitions:
            if t.event == event:
                transitions.append(t)
        return transitions


    def groupTransitionsByStartState(self, transition_list):
        if not isinstance(transition_list, list):
            raise TypeError("Invalid type for transition_list argument.")
        transition_dict = collections.OrderedDict()
        for t in transition_list:
            if t.startState not in transition_dict:
                transition_dict[t.startState] = []
            transition_dict[t.startState].append(t)
        return transition_dict


    def __str__(self):
        out = "States:\n\n"
        out += '\n\n'.join(str(s) for s in list(self.states.values()))
        out += "\n\nTransitions:\n"
        out += '\n'.join(("  " + str(t)) for t in self.transitions)
        return out
