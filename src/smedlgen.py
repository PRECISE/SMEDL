#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, unicode_literals
from smedl_parser import smedlParser
from smedl_symboltable import smedlSymbolTable
from fsm import *
from grako.ast import AST
import os
import json
import collections

def main(filename, trace=False, whitespace=None):
    with open(filename) as f:
        text = f.read()
    parser = smedlParser(parseinfo=False, comments_re="(/\*([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/)|(//.*)")
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
    # TODO: iterate through imports and make list of resulting ASTs
    symbolTable = smedlSymbolTable()
    parseToSymbolTable('top', ast, symbolTable)
    allFSMs = generateFSMs(ast, symbolTable)
    # allFSMs['default'] = makeDefaultScenario(symbolTable)
    print()
    print('Symbol Table:')
    print(symbolTable)
    print()
    print()
    for key, fsm in allFSMs.iteritems():
        print('\nFSM: %s\n'%key)
        print(fsm)
    print()
    outputSource(symbolTable, allFSMs, filename)

def parseToSymbolTable(label, object, symbolTable):
    if isinstance(object, AST):
        for k, v in object.iteritems():
            if k == 'object':
                symbolTable.add("_%s"%v, {'type' : 'object'})
            if label == 'state' and k == 'var':
                if isinstance(v, list):
                    for var in v:
                        symbolTable.add(var, {'type' : 'state', 'datatype' : object['type']})
                else:
                    symbolTable.add(v, {'type' : 'state', 'datatype' : object['type']})
            if '_events' in label and k == 'event_id':
                symbolTable.add(v, {'type' : 'event', 'error' : object['error'], 'params' : ''})
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

def generateFSMs(ast, symbolTable):
    allFSMs = collections.OrderedDict()
    for scenario in ast['scenarios'][0]:
        fsm = FSM()
        for trace in scenario['traces']: # scenario[0] is to handle redundant list structure (a grako parser thing...)
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
                    # adds parameters to symbol table for referencing in output
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
                    when = formatGuard(trace['trace_step'][i]['step_event']['when'])
                    if when == 'None':
                        when = None
                    fsm.addTransition(Transition(before_state, after_state, current, when))
                else:
                    if get(before, 'type') != 'event' or get(after, 'type') != 'event':
                        raise TypeError("Invalid state -> state transition")
        allFSMs[scenario['scenario_id']] = fsm
    return allFSMs

def makeDefaultScenario(symbolTable):
    # TODO add scenario attribute to states in symbol table
    if not symbolTable.get('STOP'):
        symbolTable.add('STOP', {'type' : 'trace_state'})
    if not symbolTable.get('RUN'):
        symbolTable.add('RUN', {'type' : 'trace_state'})
    if not symbolTable.get('default'):
        symbolTable.add('default', {'type' : 'scenarios'}) 
    fsm = FSM()
    fsm.addState(State(str('RUN')))
    fsm.addState(State(str('STOP')))
    fsm.addTransition(Transition(fsm.getStateByName(str('RUN')), fsm.getStateByName(str('STOP')), str('error')))
    fsm.addTransition(Transition(fsm.getStateByName(str('STOP')), fsm.getStateByName(str('RUN')), str('catch')))   
    return fsm 

def outputSource(symbolTable, allFSMs, filename):
    # Open file for output (based on input filename)
    out = open(os.path.splitext(filename)[0] + '_mon.c', 'w')
    out.write("#include <stdlib.h>\n\n")
    
    # Output set of states
    statesets = collections.OrderedDict()
    out.write('typedef enum { %s } scenario;\n' % (", ".join([k.upper() for k in allFSMs.keys()])))
    for key, fsm in allFSMs.iteritems():
        stateset = [("%s_%s" % (state, key)).upper() for state in fsm.states.keys()]
        statesets[key] = stateset
        stateset_str = ", ".join(stateset)
        out.write('typedef enum { ' + stateset_str + ' } %s_state;\n' % key.lower())
    errors = ['DEFAULT']
    for error in symbolTable.getSymbolsByType('event'):
        if symbolTable[error]['error']:
            errors.append(error.upper())
    out.write('typedef enum { %s } error_type;' % (", ".join(errors)))
    out.write('\n\n')
    # Output state variables
    state_vars = symbolTable.getSymbolsByType('state')
    struct = symbolTable.getSymbolsByType('object')[0]
    out.write('typedef struct %s{\n' % struct)
    if len(state_vars) > 0:   
        for v in state_vars:
            v_attrs = symbolTable.get(v)
            out.write('  ' + v_attrs['datatype'] + ' ' + v + ';\n')
        # Output initial state
    current_states = ", ".join(string.upper(stateset[0]) for key, stateset in statesets.iteritems())
    out.write("  int state[%d]; // = { %s };\n" % (len(statesets), current_states))
    out.write('} %s;\n\n' % struct)
    
    # Output catch() declaration
    out.write("void catch(%s *, int, int, error_type);\n\n" % struct)

    # Output a method for each event (switch statement to handle FSM transitions)
    methods = symbolTable.getSymbolsByType('event')
    for m in methods:
        params = symbolTable.get(m, 'params')
        if len(params) > 0:
            params = struct + "* monitor, " + params
        else:
            params = struct + "* monitor"
        out.write('void ' + m + '(' + params + ') {\n')        

        for key, fsm in allFSMs.iteritems():
            # if fsm.getTransitionsByAction(str(m)): ---------------------------------------------------------------------
            reference = 'monitor->state[%s]'%key.upper()
            out.write('  switch (%s) {\n'%reference)                
            for transition in fsm.getTransitionsByAction(str(m)):
                out.write(writeCaseTransition(transition, reference, key))
            out.write('    default:\n')      
            out.write('      catch(monitor, %s, %s, 0);\n'%(key.upper(), reference))
            out.write('      break;\n')
            out.write('  }\n')

        out.write('}\n\n')

    out.write('void catch(' + struct + ' *mon, int scen, int next_state, error_type error) {\n')
    out.write('  int recovered = 0;\n')
    out.write('  switch(error) {\n')
    for error in errors:
        out.write('    case %s:\n'%error)
        out.write('      //Call to specified function in user\'s recovery .h file\n')
        out.write('      break;\n')
    out.write('    default:\n')
    out.write('      recovered = 1;\n')
    out.write('      break;\n')
    out.write('  }\n')
    out.write('  if(recovered) {\n')
    out.write('    mon->state[scen] = next_state; //Default action\n')
    out.write('  } else {\n')
    out.write('    exit(EXIT_FAILURE);\n')
    out.write('  }\n')
    out.write('  return;\n')
    out.write('}')
    out.close()


def writeCaseTransition(trans, currentState, scenario):
    output = ['    case %s_%s:\n'%(trans.start.name.upper() ,scenario.upper())]
    if trans.guard:
        output.append('      if(' + trans.guard.replace('this.', 'monitor->') + ') {\n')
        output.append('        %s = '%currentState + ("%s_%s"%(trans.next.name, scenario)).upper() + ';\n')
        output.append('      }\n')
    else:
        output.append('      %s = '%currentState + ("%s_%s"%(trans.next.name, scenario)).upper() + ';\n')
    output.append('      break;\n')   
    return "".join(output)

def findFunctionParams(function, params, ast):
    names = []
    types = None
    if isinstance(params, AST):
        names.append(str(params['atom']))
    elif isinstance(params, list):
        for elem in params:
            if isinstance(elem, AST):
                names.append(str(elem['atom']))
    types = getParamTypes(function, ast['imported_events'])
    if types is None and ast['exported_events']:
        types = getParamTypes(function, ast['exported_events'])
    if types is None and ast['internal_events']:
        types = getParamTypes(function, ast['internal_events'])      
    if types is None: # probably never raised bc called only for events in symbol table 
        raise ValueError("Unrecognized function, %s, found in scenarios"%function) 
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
                        result = arithToString(arith, operators)
                        comps.append(" ".join(result))
                    else:
                        comps.append(termToString(val))
                return (" %s "%object['operator']).join(comps)
            elif k == 'index':
                return "[%s]"%guardToString(v)
            elif k == 'params':
                if isinstance(v, list):
                    return "(%s)"%(", ".join([guardToString(val) for val in v]))
                else:
                    return "(%s)"%guardToString(v)
            elif k == 'dot':
                trailer = ""
                if object['trailer']:
                    trailer = guardToString(object['trailer'])
                return ".%s%s"%(v, trailer)
            elif k == 'arith':
                operators = object.get('operator')
                result = arithToString(v, operators)
                return " ".join(result)
            else:
                return termToString(object)
    elif object is None:
        return ""

def arithToString(terms, operators):
    result = [None]*(len(terms)+len(operators))
    result[::2] = [termToString(term) for term in terms]
    result[1::2] = operators
    return result

def termToString(term):
    if isinstance(term, AST):
        if(term.get('arith')):
            return "(" + guardToString(term) + ")"
        unary = term.get('unary') or ""
        if isinstance(unary, list):
            unary = "".join(unary)
        term_text = "%s%s"%(unary, term.get('atom') or "")
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
