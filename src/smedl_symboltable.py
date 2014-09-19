#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, unicode_literals
from smedl_parser import smedlParser
from fsm import *
from grako.ast import AST
import os

class smedlSymbolTable(dict):

    def __init__(self):
        super(smedlSymbolTable, self).__init__()

    def add(self, symbol, attributes=None):
        if attributes is None:
            self[symbol] = {}
        else:
            self[symbol] = attributes

    def get(self, symbol, attribute=None):
        if attribute is None:
            return self[symbol]
        else:
            return self[symbol][attribute]

    def getSymbolsByType(self, type):
        out = []
        for s in self.keys():
            if 'type' in self[s] and self[s]['type'] == type :
                out.append(s)
        return out

    def update(self, symbol, attribute, value):
        self[symbol][attribute] = value

    def delete(self, symbol, attribute=None):
        if attribute is None:
            self[symbol] = None
        else:
            self[symbol][attribute] = None


def main(filename, startrule, trace=False, whitespace=None):
    import json
    with open(filename) as f:
        text = f.read()
    parser = smedlParser(parseinfo=False)
    ast = parser.parse(
        text,
        startrule,
        filename=filename,
        trace=trace,
        whitespace=whitespace)
    print('AST:')
    print(ast)
    print()
    print('JSON:')
    print(json.dumps(ast, indent=2))
    print()
    symbolTable = smedlSymbolTable()
    parseToSymbolTable('top', ast, symbolTable)
    print()
    print('Symbol Table:')
    print(symbolTable)
    print()
    fsm = generateFSM(ast, symbolTable)
    print()
    print('FSM:')
    print(fsm)
    print()
    outputSource(symbolTable, fsm, filename)

def parseToSymbolTable(label, object, symbolTable):
    if isinstance(object, AST):
        for k, v in object.iteritems():
            if label == 'state' and k == 'var':
                if isinstance(v, list):
                    for var in v:
                        symbolTable.add(var, {'type' : 'state', 'datatype' : object['type']})
                else:
                    symbolTable.add(v, {'type' : 'state', 'datatype' : object['type']})
            if '_events' in label and k == 'event_id':
                symbolTable.add(v, {'type' : 'event'})
            if label == 'traces' and k == 'trace_step':
                #print('ADDtraces: ' + k + '   ' + str(v))
                for step in v:
                    #print('ADDtraces2: ' + str(step))
                    id = step['step_event']['expression']['atom']
                    #print('ADDtraces2 id: ' + str(id))
                    if id not in symbolTable:
                        #print('ADD1: ' + k + '   ' + str(v))
                        symbolTable.add(id, {'type' : 'trace_state'})
            if ('_id' in k or k == 'atom') and v is not None and v[0].isalpha() and not (v == 'true' or v == 'false' or v == 'null') and v not in symbolTable:
                #print('ADD2: ' + label + ' ' + k + '   ' + str(v))
                symbolTable.add(v, {'type' : label})
            if isinstance(v, list):
                for vi in v:
                    parseToSymbolTable(k, vi, symbolTable)
            if isinstance(v, AST):
                #print('AST: ' + k)
                parseToSymbolTable(k, v, symbolTable)
    if isinstance(object, list):
        for elem in object:
            #print('LIST: ' + label)
            parseToSymbolTable(label, elem, symbolTable)

def generateFSM(ast, symbolTable):
    fsm = FSM()
    for scenario in ast['scenarios']:
        for trace in scenario[0]['traces']:
            for i in range(len(trace['trace_step'])):
                if i > 0 and i < (len(trace['trace_step']) - 1) and symbolTable.get(trace['trace_step'][i]['step_event']['expression']['atom'], 'type') != 'trace_state':
                    state1 = str(trace['trace_step'][i-1]['step_event']['expression']['atom'])
                    state2 = str(trace['trace_step'][i+1]['step_event']['expression']['atom'])
                    if not fsm.stateExists(state1):
                        state1 = fsm.addState(State(state1))
                        print('HERE1')
                        print(str(state1))
                    else:
                        state1 = fsm.getStateByName(state1)
                    if not fsm.stateExists(state2): #TODO: Fix problem where duplicated state is ignored and not included in AST values
                        state2 = fsm.addState(State(state2))
                        print('HERE2')
                        print(str(state2))
                    else:
                        state2 = fsm.getStateByName(state2)
                    print('HERE3')
                    print(trace['trace_step'][i]['when'])
                    fsm.addTransition(Transition(state1, state2, str(trace['trace_step'][i]['when'])))
    return fsm

def outputSource(symbolTable, fsm, filename):
    out = open(os.path.splitext(filename)[0] + '_generated.c', 'w')

    stateset = symbolTable.getSymbolsByType('trace_state')
    stateset_str = ''
    for s in stateset:
        if s is not stateset[0]:
            stateset_str += ', '
        stateset_str += string.upper(s)

    out.write('enum { ' + stateset_str + ' } stateset;\n\n')
    out.write('stateset currentState = ' + string.upper(stateset[0]) + ';\n\n')

    methods = symbolTable.getSymbolsByType('imported_events')
    for m in methods:
        out.write('void ' + m + '() {\n')
        if len(stateset) > 1:
            out.write('switch (currentState) {\n')
            for s in stateset:
                out.write('case ' + string.upper(s) + ':\n')
                out.write('currentState = ' + string.upper(s) + ';\n')
        else:
            out.write('currentState = ' + string.upper(stateset[0]) + ';\n')
        out.write('}\n\n')

    out.close()

if __name__ == '__main__':
    import argparse
    import string
    import sys

    class ListRules(argparse.Action):
        def __call__(self, parser, namespace, values, option_string):
            print('Rules:')
            for r in smedlParser.rule_list():
                print(r)
            print()
            sys.exit(0)

    parser = argparse.ArgumentParser(description="Simple parser for smedl.")
    parser.add_argument('-l', '--list', action=ListRules, nargs=0,
                        help="list all rules and exit")
    parser.add_argument('-t', '--trace', action='store_true',
                        help="output trace information")
    parser.add_argument('-w', '--whitespace', type=str, default=string.whitespace,
                        help="whitespace specification")
    parser.add_argument('file', metavar="FILE", help="the input file to parse")
    parser.add_argument('startrule', metavar="STARTRULE",
                        help="the start rule for parsing")
    args = parser.parse_args()

    main(args.file, args.startrule, trace=args.trace, whitespace=args.whitespace)
