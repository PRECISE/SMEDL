from __future__ import print_function, division, absolute_import, unicode_literals
from smedl_parser import smedlParser
from smedl_symboltable import smedlSymbolTable
from fsm import *
from grako.ast import AST
import os
import json
import unittest

class TestSmedlgen(unittest.TestCase):

    def setUp(self):
        self.writer = SmedlWriter("Thing")

    def test_writer(self):
        self.writer.add_i("iiii1")
        self.writer.add_i("iiii2")
        self.writer.add_st("stststs")
        self.writer.add_e("eee1")
        self.writer.add_e("eee2")
        self.writer.add_sc("sc1")
        self.writer.add_t("sc1", "A -> ab -> B")
        self.writer.add_t("sc1", "A -> bd -> D")
        self.writer.add_t("sc1", "B -> bc -> C")
        self.writer.rm_i(0)
        self.writer.rm_t("sc1", 1)
        print(self.writer.text)     

class SmedlWriter(object):

    def __init__(self, identifier):
        self.id = identifier
        self.identity = []
        self.state = []
        self.events = []
        self.scenarios = dict()
        self.build()

    def add_i(self, identity):
        self.identity.append(identity)
        self.build()

    def add_st(self, state):
        self.state.append(state)
        self.build()

    def add_e(self, event):
        self.events.append(event)
        self.build()

    def add_sc(self, scenario):
        self.scenarios[scenario] = []
        self.build()

    def add_t(self, scenario, trace):
        self.scenarios[scenario].append(trace)
        self.build()

    def rm_i(self, identity_index):
        del self.identity[identity_index]
        self.build()

    def rm_st(self, state_index):
        del self.state[state_index]
        self.build()

    def rm_e(self, event_index):
        del self.events[event_index]
        self.build()

    def rm_sc(self, scenario):
        self.scenarios.pop(scenario)
        self.build()

    def rm_t(self, scenario, trace_index):
        del self.scenarios[scenario][trace_index]
        self.build()

    def build(self):
        self.text = "object %s\n"%self.id
        if(self.identity):
            self.text += "identity\n"
            for i in self.identity:
                self.text += "\t%s;\n"%i
        if(self.state):
            self.text += "state\n"
            for s in self.state:
                self.text += "\t%s;\n"%s
        if(self.events):
            self.text += "events\n"
            for e in self.events:
                self.text += "\t%s;\n"%e
        if(self.scenarios):
            self.text += "scenarios\n"
            for s in self.scenarios.keys():
                self.text += "\t%s:\n"%s
                for t in self.scenarios[s]:
                    self.text +="\t\t%s\n"%t

if __name__ == '__main__':
    unittest.main()
