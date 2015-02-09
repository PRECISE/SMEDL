#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, unicode_literals
from smedl_parser import smedlParser
from smedl_symboltable import smedlSymbolTable
from fsm import *
from grako.ast import AST
import os
import json

def main(filename, trace=False, whitespace=None):
    with open(filename) as f:
        text = f.read()
    parser = smedlParser(parseinfo=False, comments_re="\(\*.*?\*\)")
    ast = parser.parse(
        text,
        'object',
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
    fsm = generateFSM(ast, symbolTable)
    print()
    print('Symbol Table:')
    print(symbolTable)
    print()
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
        for trace in scenario[0]['traces']: # scenario[0] is to handle redundant list structure (a grako parser thing...)
            generated_state = None
            before_state = None
            after_state = None
            for i in range(1, len(trace['trace_step']) - 1):
                current = str(trace['trace_step'][i]['step_event']['expression']['atom'])
                if generated_state is None:
                    before = str(trace['trace_step'][i-1]['step_event']['expression']['atom'])
                else:
                    before = generated_state
                    generated_state = None
                after = str(trace['trace_step'][i+1]['step_event']['expression']['atom'])
                if symbolTable.get(current,'type') == 'event':
                    params = trace['trace_step'][i]['step_event']['expression']['trailer']['params']
                    param_names = str(findFunctionParams(current, params, ast))
                    symbolTable.update(current, "params", param_names)
                    if not fsm.stateExists(before):
                        fsm.addState(State(before))
                    if symbolTable.get(after, 'type') == 'trace_state':
                        if not fsm.stateExists(after):
                            fsm.addState(State(after))
                    else:
                        after = symbolTable.generate({'type' : 'trace_state'})
                        fsm.addState(State(after))
                        generated_state = after
                    before_state = fsm.getStateByName(before)
                    after_state = fsm.getStateByName(after)
                    current = str("%s(%s)"%(current, param_names))
                    when = formatGuard(trace['trace_step'][i]['step_event']['when'])
                    if when == 'None':
                        when = None
                    fsm.addTransition(Transition(before_state, after_state, current, when))
                else:
                    if get(before, 'type') != 'event' or get(after, 'type') != 'event':
                        raise TypeError("Invalid state -> state transition")
    return fsm

def outputSource(symbolTable, fsm, filename):
    # Open file for output (based on input filename)
    out = open(os.path.splitext(filename)[0] + '_generated.c', 'w')

    # Output set of states
    stateset = [state.upper() for state in fsm.states.keys()]
    stateset_str = ", ".join(stateset)
    out.write('enum { ' + stateset_str + ' } stateset;\n\n')

    # Output state variables
    state_vars = symbolTable.getSymbolsByType('state')
    if len(state_vars) > 0:
        out.write('struct {\n')
        for v in state_vars:
            v_attrs = symbolTable.get(v)
            out.write('  ' + v_attrs['datatype'] + ' ' + v + ';\n')
        out.write('};\n')

    # Output initial state
    out.write('stateset currentState = ' + string.upper(stateset[0]) + ';\n\n')

    # Output a method for each event (switch statement to handle FSM transitions)
    methods = symbolTable.getSymbolsByType('event')
    for m in methods:
        out.write('void ' + m + '(' + symbolTable.get(m, 'params') + ') {\n')
        if len(stateset) > 1:
            out.write('  switch (currentState) {\n')
            for t in fsm.getTransitionsByAction(str(m)):
                out.write('    case ' + string.upper(t.start.name) + ':\n')
                if t.guard is not None:
                    out.write('      if(' + t.guard + ') {\n')
                    out.write('        currentState = ' + string.upper(t.next.name) + ';\n')
                    out.write('      }\n')
                else:
                    out.write('      currentState = ' + string.upper(t.next.name) + ';\n')
                out.write('      break;\n')
            out.write('  }\n')
        else:
            out.write('  currentState = ' + string.upper(stateset[0]) + ';\n')
        out.write('}\n\n')

    out.close()

def findFunctionParams(function, params, ast):
    names = []
    types = None
    if isinstance(params, AST):
        names.append(str(params['atom']))
    elif isinstance(params, list):
        for elem in params:
            if isinstance(elem, AST):
                names.append(str(elem['atom']))
    types = getParamTypes(function, ast['imported_events'][0])
    if types is None and ast['exported_events'] is not None:
        types = getParamTypes(function, ast['exported_events'][0])
    if types is None:
        types = []
    if len(names) != len(types):
        raise ValueError("Invalid number of parameters for %s"%function)
    return (", ".join(["%s %s"%(types[i],names[i]) for i in range(len(names))]))

def getParamTypes(function, events):
    if isinstance(events, AST):
        if(events['event_id'] == function):
            params = events['params']
            types = []
            if(params):
                if isinstance(params, list):
                    types = [str(p) for p in params]
                else:
                    types.append(str(params))
            return types
        else:
            return None
    elif isinstance(events, list):
        for elem in events:
            types = getParamTypes(function, elem)
            if types is not None:
                return types
        return None

def formatGuard(object):
    guard = str(guardToString(object))
    return removeParentheses(guard)

def guardToString(object):
    if isinstance(object, AST):
        for k, v in object.iteritems():
            if k == 'or_ex':
                ored = [guardToString(val) for val in v]
                return "(" + " || ".join(ored) + ")"
            elif k == 'and_ex':
                anded = [guardToString(val) for val in v]
                return "(" + " && ".join(anded) + ")" 
            elif k == 'not_ex':
                return "!(%s)"%guardToString(v)      
            elif k == 'comp':
                comps = []
                for val in v:
                    arith = val.get('arith')
                    if arith:
                        operators = val.get('operator')
                        result = [None]*(len(arith)+len(operators))
                        result[::2] = [termToString(term) for term in arith]
                        result[1::2] = operators
                        comps.append(" ".join(result))
                    else:
                        comps.append(termToString(val))
                return (" %s "%object['operator']).join(comps)
            elif k == 'index':
                return "[%s]"%guardToString(v)
            elif k == 'params':
                if isinstance(v, list):
                    return "(%s)"%(",".join([guardToString(val) for val in v]))
                else:
                    return "(%s)"%guardToString(v)
            elif k == 'dot':
                trailer = ""
                if object['trailer']:
                    trailer = guardToString(object['trailer'])
                return ".%s%s"%(v, trailer)
            else:
                return termToString(object)

def termToString(term):
    if isinstance(term, AST):
        term_text = "%s%s"%(term.get('unary') or "", term.get('atom') or "")
        trailer_ast = term.get('trailer')
        if isinstance(trailer_ast, AST):
            for k, v in term.iteritems():
                term_text = "%s%s"%(term_text, guardToString(v) or "")
        return term_text
    else:
        return ""

def removeParentheses(guard):
    if guard.startswith('(') and guard.endswith(')'):
        stack = ['s']
        for ch in guard[1:-1]:
            if ch == '(':
                stack.append('(')
            if ch == ')':
                stack.pop()
        if len(stack) == 1 and stack[0] == 's':
            return removeParentheses(guard[1:-1])
        else:
            return guard
    else:
        return guard


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
    args = parser.parse_args()

    main(args.file, trace=args.trace, whitespace=args.whitespace)
