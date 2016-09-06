#!/usr/bin/env python
# -*- coding: utf-8 -*-

#-------------------------------------------------------------------------------
# mgen.py
#
# Peter Gebhard (pgeb@seas.upenn.edu)
#-------------------------------------------------------------------------------

from .parser import *
from .fsm import *
from .c_style import *
from grako.ast import AST
from jinja2 import Environment, PackageLoader
import json
import collections
import re
import shutil
import string
from pathlib import Path

# Turn a list of arguments into an argument string for using in a generated
# method call. prefix determines whether a leading comma is prepended when the
# argument list is not empty.
#
# args : list of strings. The arguments to turn into an argument string.
# prefix : boolean. Whether to prefix a comma when the list is non-empty.
def joinArgs(args, prefix=""):
    if (not args):
        return ""
    else:
        return prefix + ", ".join(args)


class MonitorGenerator(object):

    def __init__(self, structs=False, debug=False, implicit=True):
        self._symbolTable = SmedlSymbolTable()
        self._printStructs = structs
        self._debug = debug
        self._implicitErrors = implicit
        self.pedlAST = None
        self.smedlAST = None


    def generate(self, pedlsmedlName, helper=None):
        # Parse the PEDL, if it exists
        pedlPath = Path(pedlsmedlName + '.pedl')
        if pedlPath.exists():
            with pedlPath.open() as pedlFile:
                pedlText = pedlFile.read()
            pedlPar = pedlParser(
                parseinfo=False,
                comments_re="(/\*([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/)|(//.*)",
                semantics=pedlModelBuilderSemantics())
            self.pedlAST = pedlPar.parse(
                pedlText,
                'object',
                filename=pedlPath,
                trace=False,
                whitespace=None)
            if self._printStructs:
                print('PEDL AST:')
                print(self.pedlAST)

        # Parse the SMEDL, if it exists
        smedlPath = Path(pedlsmedlName + '.smedl')
        if smedlPath.exists():
            with smedlPath.open() as smedlFile:
                smedlText = smedlFile.read()
            smedlPar = smedlParser(
                parseinfo=False,
                comments_re="(/\*([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/)|(//.*)")
            self.smedlAST = smedlPar.parse(
                smedlText,
                'object',
                filename=smedlPath,
                trace=False,
                whitespace=None)
            if self._printStructs:
                print('SMEDL AST:')
                print(self.smedlAST)
                print('\nSMEDL JSON:')
                print(json.dumps(self.smedlAST, indent=2))
        else:
            if '.smedl' in pedlsmedlName or '.pedl' in pedlsmedlName:
                raise ValueError('Did you accidentally include .smedl or .pedl in the input filename? Try again without including the extension.')
            raise ValueError('No matching SMEDL file found.')

        # Process the SMEDL AST
        self._symbolTable = SmedlSymbolTable()
        self._parseToSymbolTable('top', self.smedlAST)
        self._getParameterNames(self.smedlAST)
        allFSMs = self._generateFSMs(self.smedlAST)

        # Output the internal symbol table and FSMs
        if self._printStructs:
            print('\nSMEDL Symbol Table:')
            for k in self._symbolTable:
                print('%s: %s' % (k, self._symbolTable[k]))
            for key, fsm in list(allFSMs.items()):
                print('\nFSM: %s\n' % key)
                print('%s\n' % fsm)

        CTemplater.output(self, allFSMs, pedlsmedlName, helper, self.pedlAST)


    def _parseToSymbolTable(self, label, object):
        if isinstance(object, AST):
            for k, v in list(object.items()):
                if k == 'object':
                    self._symbolTable.add(v, {'type': 'object'})
                elif label == 'identity' and k == 'var':
                    if isinstance(v, list):
                        for var in v:
                            self._symbolTable.add(var, {'type': 'identity', 'datatype': object['type']})
                    else:
                        self._symbolTable.add(v, {'type': 'identity', 'datatype': object['type']})
                elif label == 'state' and k == 'var':
                    if isinstance(v, list):
                        for var in v:
                            self._symbolTable.add(var, {'type': 'state', 'datatype': object['type']})
                    else:
                        self._symbolTable.add(v, {'type': 'state', 'datatype': object['type']})
                elif '_events' in label and k == 'event_id':
                    self._symbolTable.add(v, {'type': label, 'error': object['error'], 'params': object['params']})
                elif label == 'traces':
                    if '_state' in k and v is not None:
                        self._symbolTable.add(v, {'type': 'trace_state'})
                elif ('_id' in k or k == 'atom') and v is not None and v[0].isalpha() and not \
                    (v == 'true' or v == 'false' or v == 'null' or v == 'this') and v not in self._symbolTable:
                        self._symbolTable.add(v, {'type': label})
                self._parseToSymbolTable(k, v)
        if isinstance(object, list):
            for elem in object:
                self._parseToSymbolTable(label, elem)


    def _getParameterNames(self, ast):
        for scenario in ast['scenarios'][0]:  # [0] handles grako's nested list structure
            for trace in scenario['traces']:
                for i in range(0, len(trace['trace_steps'])):
                    current = trace['trace_steps'][i]['step_event']['expression']['atom']
                    if 'event' in self._symbolTable.get(current, 'type'):
                        # Handle events with no parameters defined:
                        if trace['trace_steps'][i]['step_event']['expression']['trailer'] is None:
                            self._symbolTable.update(current, "params", [])
                        else:
                            params = trace['trace_steps'][i]['step_event']['expression']['trailer']['params']
                            paramsList = self._findFunctionParams(current, params, ast)
                            self._symbolTable.update(current, "params", paramsList)
                    if trace['trace_steps'][i]['step_actions'] is not None:
                        for j in range(0, len(trace['trace_steps'][i]['step_actions']['actions'])):
                            # Handle raise statement
                            step_actions_islist = isinstance(trace['trace_steps'][i]['step_actions']['actions'], list)
                            if (step_actions_islist and trace['trace_steps'][i]['step_actions']['actions'][j]['raise_stmt'] is not None) or (not step_actions_islist and trace['trace_steps'][i]['step_actions']['actions']['raise_stmt'] is not None):
                                if step_actions_islist:
                                    current = trace['trace_steps'][i]['step_actions']['actions'][j]['raise_stmt']
                                else:
                                    current = trace['trace_steps'][i]['step_actions']['actions']['raise_stmt']
                                if 'event' in self._symbolTable.get(current['id'], 'type'):
                                    # Handle events with no parameters defined:
                                    if current['expr_list'][0] is None:
                                        self._symbolTable.update(current['id'], "params", [])
                                    else:
                                        params = current['expr_list']
                                        paramsList = self._findFunctionParams(current['id'], params, ast)
                                        self._symbolTable.update(current['id'], "params", paramsList)
                if trace['else_actions'] is not None:
                    for i in range(0, len(trace['else_actions']['actions'])):
                        # Handle raise statement
                        else_actions_islist = isinstance(trace['else_actions']['actions'], list)
                        if (else_actions_islist and trace['else_actions']['actions'][i]['raise_stmt'] is not None) or (not else_actions_islist and trace['else_actions']['actions']['raise_stmt'] is not None):
                            if else_actions_islist:
                                current = trace['else_actions']['actions'][i]['raise_stmt']
                            else:
                                current = trace['else_actions']['actions']['raise_stmt']
                            if 'event' in self._symbolTable.get(current['id'], 'type'):
                                # Handle events with no parameters defined:
                                if current['expr_list'][0] is None:
                                    self._symbolTable.update(current['id'], "params", [])
                                else:
                                    params = current['expr_list']
                                    paramsList = self._findFunctionParams(current['id'], params, ast)
                                    self._symbolTable.update(current['id'], "params", paramsList)


    def _generateFSMs(self, ast):
        allFSMs = collections.OrderedDict()

        # Go through each scenario and build an FSM
        for scenario in ast['scenarios'][0]:  # [0] handles grako's nested list structure
            fsm = FSM()

            # Go through each trace in the scenario
            for trace in scenario['traces']:

                # Handle the Else bits
                elseState = None
                elseActions = None
                if trace['else_state']:
                    elseState = trace['else_state']
                    if not fsm.stateExists(elseState):
                        fsm.addState(State(elseState))
                    elseState = fsm.getStateByName(elseState)
                    if trace['else_actions']:
                        elseActions = []
                        astActions = trace['else_actions']['actions']
                        if not isinstance(astActions,list):
                            astActions = [astActions]
                        for action in astActions:
                            if action['state_update']:
                                elseActions.append(StateUpdateAction(action['state_update']['target'], action['state_update']['operator'], action['state_update']['expression']))
                            if action['raise_stmt']:
                                if self._debug:
                                    print("ELSE ACTION RAISE DEBUG: " + str(action['raise_stmt']['expr_list']))
                                    print(action)
                                elseActions.append(RaiseAction(action['raise_stmt']['id'], action['raise_stmt']['expr_list']))
                            if action['instantiation']:
                                elseActions.append(InstantiationAction(action['instantiation']['id'], action['instantiation']['state_update_list']))
                            if action['call_stmt']:
                                elseActions.append(CallAction(action['call_stmt']['target'], action['call_stmt']['expr_list']))

                # Handle the traces
                generated_state = None
                for i in range(0, len(trace['trace_steps'])):
                    current = trace['trace_steps'][i]['step_event']['expression']['atom']
                    if i == 0:
                        before = trace['start_state']
                    else:
                        before = trace['trace_steps'][i-1]['step_event']['expression']['atom']
                    if i == len(trace['trace_steps']) - 1:
                        after = trace['end_state']
                    else:
                        after = trace['trace_steps'][i+1]['step_event']['expression']['atom']

                    if generated_state is not None:
                        before = generated_state
                        generated_state = None

                    if 'event' in self._symbolTable.get(current, 'type'):
                        actions = None
                        if trace['trace_steps'][i]['step_actions']:
                            actions = []
                            astActions = trace['trace_steps'][i]['step_actions']['actions']
                            if not isinstance(astActions,list):
                                astActions = [astActions]
                            for action in astActions:
                                if action['state_update']:
                                    actions.append(StateUpdateAction(action['state_update']['target'], action['state_update']['operator'], action['state_update']['expression']))
                                if action['raise_stmt']:
                                    if self._debug:
                                        print("STEP ACTION RAISE DEBUG: " + str(action['raise_stmt']['expr_list']))
                                        print(action)
                                    actions.append(RaiseAction(action['raise_stmt']['id'], action['raise_stmt']['expr_list']))
                                if action['instantiation']:
                                    actions.append(InstantiationAction(action['instantiation']['id'], action['instantiation']['state_update_list']))
                                if action['call_stmt']:
                                    actions.append(CallAction(action['call_stmt']['target'], action['call_stmt']['expr_list']))
                        if not fsm.stateExists(before):
                            fsm.addState(State(before))
                        if self._symbolTable.get(after, 'type') == 'trace_state':
                            if not fsm.stateExists(after):
                                fsm.addState(State(after))
                        else:
                            after = self._symbolTable.generateSymbol({'type': 'trace_state'})
                            fsm.addState(State(after))
                            generated_state = after
                        before_state = fsm.getStateByName(before)
                        after_state = fsm.getStateByName(after)
                        when = self._formatExpression(trace['trace_steps'][i]['step_event']['when'])
                        if when == 'None':
                            when = None
                        fsm.addTransition(Transition(before_state, current, after_state, actions, when, elseState, elseActions))
                    else:
                        if i > 0:
                            raise TypeError("Named states only valid at beginning/end of trace. Invalid: %s" % current)
                        if 'event' not in self._symbolTable.get(before, 'type') or 'event' not in self._symbolTable.get(after, 'type'):
                            raise TypeError("Invalid state to state transition: %s -> %s" % (before, after))

                # Set the start state
                if fsm.startState is None:
                    fsm.startState = fsm.getStateByName(trace['start_state'])

            allFSMs[scenario['scenario_id']] = fsm
        return allFSMs


    def _findFunctionParams(self, function, params, ast):
        names = []
        types = None
        if isinstance(params, AST):
            names.append(str(params['atom']))
        elif isinstance(params, list):
            if isinstance(params[0], list):
                params = params[0] # Unpack from extra list wrapping
            for elem in params:
                if isinstance(elem, AST):
                    names.append(str(elem['atom']))
        types = self._getParamTypes(function, ast['imported_events'])
        if types is None and ast['exported_events']:
            types = self._getParamTypes(function, ast['exported_events'])
        if types is None and ast['internal_events']:
            types = self._getParamTypes(function, ast['internal_events'])
        if types is None:  # probably never raised - called only for events in symbolTable
            raise ValueError("Unrecognized function, %s, found in scenarios" % function)

        if self._debug:
            print ("*** Finding function parameters ***")
            print("Function name: ", function)
            print("Function params: ", params)
            print("Param names: ", names)
            print("Param types: ", types)

        if len(names) != len(types):
            raise ValueError("Invalid number of parameters for %s" % function)
        return [{'type':types[i], 'true_name':names[i], 'name':'mon_var_'+names[i]} for i in range(len(names))]


    def _getParamTypes(self, function, events):
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
                types = self._getParamTypes(function, elem)
                if types is not None:
                    return types
            return None


    def _formatExpression(self, expr):
        if expr is None:
            expr = ""
        if isinstance(expr, AST):
            exprStr = AstToPython.expr(expr)
        else:
            exprStr = expr
        exprStr = self._addMonitorArrowToStateVariables(exprStr)
        # expr = checkReferences(expr) # TODO--------
        return MonitorGenerator._removeParentheses(exprStr)


    def _addMonitorArrowToStateVariables(self, string):
        for sv in self._symbolTable.getSymbolsByType('state'):
            indices = [t.start() for t in re.finditer(sv, string)]
            for index in indices:
                if string[index-5:index] != 'this.' and string[index-9:index] != 'monitor->':  # Prevent duplicated 'this.'
                    string = string[:index] + 'monitor->' + string[index:]
        return string

    @staticmethod
    def _removeParentheses(guard):
        if guard.startswith('(') and guard.endswith(')'):
            stack = ['s']
            for ch in guard[1:-1]:
                if ch == '(':
                    stack.append('(')
                if ch == ')':
                    stack.pop()
            if len(stack) == 1 and stack[0] == 's':
                return MonitorGenerator._removeParentheses(guard[1:-1])
            else:
                return guard
        else:
            return guard

    @staticmethod
    def _checkReferences(guard):
        re.findall(r'\s([A-Za-z_]\w*).\w+\W+', guard)


    def _writeAction(self, obj, action):
        if action.type == ActionType.StateUpdate:
            out = "monitor->" + action.target + ' ' + action.operator
            if action.expression:
                out += ' ' + self._formatExpression(action.expression)
            out += ';'
            return out
        elif action.type == ActionType.Raise:
            return 'raise_%s_%s(monitor%s);' % (obj.lower(), action.event, joinArgs([self._formatExpression(p) for p in action.params], ", "))
        elif action.type == ActionType.Instantiation:
            exit("Instantiation actions are not implemented. Sorry!")
        elif action.type == ActionType.Call:
            out = action.target + '('
            paramCount = len(action.params)
            c = 0
            for param in action.params:
                out += param
                c += 1
                if c != paramCount:
                    out += ','
            out += ');'
            return out

    # ALTERNATIVE ACTION QUEUE CODE
    #         output = []
    #         output.append('    case %s: ;' % event.upper())
    #         paramString = ','.join(['%s %s'%(p['type'], p['name']) for p in self._symbolTable.get(event, 'params')])
    #         if paramString == '':
    #             output.append('      %s(monitor);' % event)
    #         else:
    #             params = self._getEventParams(paramString)
    #             for p in params:
    #                 output.append('      %s %s_%s = monitor->action_queue->params->%c;' % (p[0], p[1], event, p[0][0]))
    #                 output.append('      pop_param(&monitor->action_queue->params);')
    #             callParams = ", ".join('%s_%s' % (p[1], event) for p in params)
    #             output.append('      %s(%s);' % (event, ", ".join(['monitor', callParams])))
    #         output.append('      break;')
    #         return '\n'.join(output)


    def _getEventParams(paramString):
        paramsList = []
        params = [str(s) for s in paramString.split(', ')]
        for p in params:
            paramsList.append([str(s) for s in p.split(' ')])
        return paramsList


import argparse

def main():
    parser = argparse.ArgumentParser(description="Code Generator for SMEDL and PEDL.")
    parser.add_argument('--helper', help='Include header file for helper functions')
    parser.add_argument('-s', '--structs', help='Print internal data structures', action='store_true')
    parser.add_argument('-d', '--debug', help='Show debug output', action='store_true')
    parser.add_argument('--noimplicit', help='Disable implicit error handling in generated monitor', action='store_false')
    # TODO: Add version flag
    parser.add_argument('pedlsmedl', metavar="pedl_smedl_filename", help="the name of the PEDL and SMEDL files to parse")
    args = parser.parse_args()

    mgen = MonitorGenerator(structs=args.structs, debug=args.debug, implicit=args.noimplicit)
    mgen.generate(args.pedlsmedl, helper=args.helper)

if __name__ == '__main__':
    main()
