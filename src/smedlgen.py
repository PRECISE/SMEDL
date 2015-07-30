#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, \
    unicode_literals
from smedl_parser import smedlParser
from pedl_parser import pedlParser
from smedl_symboltable import smedlSymbolTable
from fsm import *
from grako.ast import AST
from jinja2 import Environment, FileSystemLoader
import os
import json
import collections
import re
import shutil


def main(pedlFilename, smedlFilename, helper=None):
    # Parse the PEDL
    with open(pedlFilename) as pedlFile:
        pedlText = pedlFile.read()
    pedlPar = pedlParser(
        parseinfo=False,
        comments_re="(/\*([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/)|(//.*)")
    pedlAST = pedlPar.parse(
        pedlText,
        'object',
        filename=pedlFilename,
        trace=False,
        whitespace=None)
    print('PEDL AST:')
    print(pedlAST)
    print('\nPEDL JSON:')
    print(json.dumps(pedlAST, indent=2))

    # Parse the SMEDL
    with open(smedlFilename) as smedlFile:
        smedlText = smedlFile.read()
    smedlPar = smedlParser(
        parseinfo=False,
        comments_re="(/\*([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/)|(//.*)")
    smedlAST = smedlPar.parse(
        smedlText,
        'object',
        filename=smedlFilename,
        trace=False,
        whitespace=None)
    print('SMEDL AST:')
    print(smedlAST)
    print('\nSMEDL JSON:')
    print(json.dumps(smedlAST, indent=2))

    # Process the SMEDL AST
    smedlST = smedlSymbolTable()
    parseToSymbolTable('top', smedlAST, smedlST)
    allFSMs = generateFSMs(smedlAST, smedlST)
    print('\nSMEDL Symbol Table:')
    for k in smedlST:
        print('%s: %s'%(k, smedlST[k]))
    for key, fsm in allFSMs.iteritems():
        print('\nFSM: %s\n' % key)
        print('%s\n'%fsm)
    #outputSource(smedlST, allFSMs, smedlFilename, helper)
    outputToTemplate(smedlST, allFSMs, smedlFilename, helper)


def parseToSymbolTable(label, object, symbolTable):
    if isinstance(object, AST):
        for k, v in object.iteritems():
            if k == 'object':
                symbolTable.add(v, {'type': 'object'})
            elif label == 'identity' and k == 'var':
                if isinstance(v, list):
                    for var in v:
                        symbolTable.add(var, {'type': 'identity', 'datatype': object['type']})
                else:
                    symbolTable.add(v, {'type': 'identity', 'datatype': object['type']})             
            elif label == 'state' and k == 'var':
                if isinstance(v, list):
                    for var in v:
                        symbolTable.add(var, {'type': 'state', 'datatype': object['type']})
                else:
                    symbolTable.add(v, {'type': 'state', 'datatype': object['type']})
            elif '_events' in label and k == 'event_id':
                symbolTable.add(v, {'type': label, 'error': object['error'], 'params': object['params']})
            elif label == 'traces':
                if '_state' in k and v is not None:
                    symbolTable.add(v, {'type': 'trace_state'})
            elif ('_id' in k or k == 'atom') and v is not None and v[0].isalpha() and not \
                (v == 'true' or v == 'false' or v == 'null' or v == 'this') and v not in symbolTable:
                symbolTable.add(v, {'type': label})
            parseToSymbolTable(k, v, symbolTable)
    if isinstance(object, list):
        for elem in object:
            parseToSymbolTable(label, elem, symbolTable)


def generateFSMs(ast, symbolTable):
    allFSMs = collections.OrderedDict()

    # Go through each scenario and build an FSM
    for scenario in ast['scenarios'][0]: #[0] handles grako's nested list structure
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
                if trace['else_action']:
                    elseActions = []
                    for action in trace['else_action']['actions']:
                        if action['state_update']:
                            elseActions.append('state_update: ' + action['state_update']['target'])
                        if action['raise_stmt']:
                            elseActions.append('raise: ' + action['raise_stmt']['id'])
                        if action['instantiation']:
                            elseActions.append('instantiation: ' + action['instantiation']['id'])
                        if action['call_stmt']:
                            elseActions.append('call: ' + action['call_stmt']['target'])

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

                if 'event' in symbolTable.get(current, 'type'):
                    actions = None
                    if trace['trace_steps'][i]['step_action']:
                        actions = []
                        for action in trace['trace_steps'][i]['step_action']['actions']:
                            if action['state_update']:
                                actions.append('state_update: ' + action['state_update']['target'])
                            if action['raise_stmt']:
                                actions.append('raise: ' + action['raise_stmt']['id'])
                            if action['instantiation']:
                                actions.append('instantiation: ' + action['instantiation']['id'])
                            if action['call_stmt']:
                                actions.append('call: ' + action['call_stmt']['target'])

                    # add parameters to symbol table for referencing in output
                    params = trace['trace_steps'][i]['step_event']['expression']['trailer']['params']
                    param_names = str(findFunctionParams(current, params, ast))
                    symbolTable.update(current, "params", param_names)

                    if not fsm.stateExists(before):
                        fsm.addState(State(before))
                    if symbolTable.get(after, 'type') == 'trace_state':
                        if not fsm.stateExists(after):
                            fsm.addState(State(after))
                    else:
                        after = symbolTable.generate({'type': 'trace_state'})
                        fsm.addState(State(after))
                        generated_state = after
                    before_state = fsm.getStateByName(before)
                    after_state = fsm.getStateByName(after)
                    when = formatGuard(trace['trace_steps'][i]['step_event']['when'])
                    if when == 'None':
                        when = None
                    fsm.addTransition(Transition(before_state, current, after_state, actions, when, elseState, elseActions))
                else:
                    if i > 0:
                        raise TypeError("Named states only valid at beginning/end of trace. Invalid: %s"%current)
                    if 'event' not in symbolTable.get(before, 'type') or 'event' not in symbolTable.get(after, 'type'):
                        raise TypeError("Invalid state -> state transition: %s -> %s"%(before, after))
        allFSMs[scenario['scenario_id']] = fsm
    return allFSMs


# def outputSource(symbolTable, allFSMs, filename, helper):
#     # Open file for output (based on input filename)
#     out = open(os.path.splitext(filename)[0] + '_mon_test.c', 'w') #testing .c and .h
#     header = open(os.path.splitext(filename)[0] + '_mon_test.h', 'w') #testing .c and .h
#     out.write("#include <stdlib.h>\n")
#     out.write("#include <stdio.h>\n")
#     out.write("#include \"actions.h\"\n")
#     if helper:
#         out.write("#include \"%s\"\n"%helper)
#     out.write("\n")

#     # Output set of states
#     statesets = collections.OrderedDict()
#     out.write('typedef enum { %s } scenario;\n' % (", ".join([k.upper() for k in allFSMs.keys()])))
#     state_enums = []
#     state_names_arrays = []
#     for key, fsm in allFSMs.iteritems():
#         stateset = [("%s_%s" % (state, key)).upper() for state in fsm.states.keys()]
#         statesets[key] = stateset
#         stateset_str = ", ".join(stateset)
#         state_enums.append('typedef enum { ' + stateset_str + ' } %s_state;\n' % key.lower())
#         state_names = ", ".join(['\"%s\"'%(state) for state in fsm.states.keys()])
#         state_names_arrays.append('const char *%s_states[%d] = {%s};\n'%(key, len(fsm.states.keys()), state_names))
#     out.write(''.join(state_enums))
#     events = [str(e).upper() for e in symbolTable.getEvents()]
#     errors = ['DEFAULT']
#     for e in symbolTable.getSymbolsByType('event'):
#         if symbolTable[e]['error']:
#             errors.append(e.upper())
#     out.write('typedef enum { %s } event;\n' % (", ".join(events)))
#     out.write('typedef enum { %s } error_type;\n' % (", ".join(errors)))
#     out.write(''.join(state_names_arrays))
#     out.write('\n')

#     # Output state variables
#     state_vars = symbolTable.getSymbolsByType('state')
#     struct = symbolTable.getSymbolsByType('object')[0]
#     out.write('typedef struct %s{\n' % struct)
#     if len(state_vars) > 0:
#         for v in state_vars:
#             v_attrs = symbolTable.get(v)
#             out.write('  ' + v_attrs['datatype'] + ' ' + v + ';\n')
#         # Output initial state
#     current_states = ", ".join(string.upper(stateset[0]) for key, stateset in statesets.iteritems())
#     out.write("  int state[%d]; // = { %s };\n" % (len(statesets), current_states))
#     out.write("  const char **state_names[%d];\n" % (len(statesets)))
#     out.write("  action *action_queue;\n")
#     out.write('} %s;\n\n' % struct)

#     # Output catch() declaration
#     out.write("void call_next_action(%s*);\n"%struct)
#     out.write("void raise_error(char*, const char*, char*, char*);\n\n")

#     out.write("%s* init%s() {\n"%(struct, struct))
#     out.write("  %s* monitor = (%s*)malloc(sizeof(%s));\n"%(struct,struct,struct))
#     scenario_index = 0
#     init_current = []
#     init_names = []
#     for key, fsm in allFSMs.iteritems():
#         init_current.append("  monitor->state[%d] = %s_%s;\n"%(scenario_index, next(iter(fsm.states)).upper(), key.upper()))
#         init_names.append("  monitor->state_names[%d] = %s_states;\n"%(scenario_index, key))
#         scenario_index += 1
#     out.write(''.join(init_current))
#     out.write(''.join(init_names))

#     out.write("  return monitor;\n}\n\n")

#     # Output a method for each event (switch statement to handle FSM transitions)
#     methods = symbolTable.getEvents()
#     callCases = []
#     for m in methods:
#         params = symbolTable.get(m, 'params')
#         if len(params) > 0:
#             params = struct + "* monitor, " + params
#         else:
#             params = struct + "* monitor"
#         out.write('void ' + m + '(' + params + ') {\n')

#         for key, fsm in allFSMs.iteritems():
#             reference = 'monitor->state[%s]' % key.upper()
#             name_reference = "monitor->state_names[%s][monitor->state[%s]]"%(key.upper(), key.upper())
#             out.write('  switch (%s) {\n' % reference)
#             for transition in fsm.getTransitionsByEvent(str(m)):
#                 out.write(writeCaseTransition(transition, reference, name_reference, key, m))
#             out.write('    default:\n')
#             out.write('      raise_error(\"%s\", %s, \"%s\", \"DEFAULT\");\n'%(key, name_reference, m))
#             out.write('      break;\n')
#             out.write('  }\n')

#         #move
#         callCases.append(writeCallCase(symbolTable, m))

#         out.write('}\n\n')

#         out.write(writeRaiseFunction(symbolTable, m, struct))

#     for s in state_vars:
#         out.write('void set%s_%s(%s *monitor, %s new_%s) {\n'%(struct.lower(), s, struct,
#             symbolTable.get(s)['datatype'], s))
#         out.write('  monitor->%s = new_%s;\n  return;\n}\n\n'%(s, s))

#     out.write('void call_next_action(%s *monitor) {\n'%struct)
#     out.write('  switch (monitor->action_queue->id) {\n')
#     out.write('\n'.join(callCases))
#     out.write('\n  }\n}\n\n')

#     out.write('void exec_actions(%s *monitor) {\n'%struct)
#     out.write('  while(monitor->action_queue != NULL) {\n')
#     out.write('    call_next_action(monitor);\n')
#     out.write('    pop_action(&monitor->action_queue);\n')
#     out.write('  }\n}\n\n')
#     out.write("void raise_error(char *scen, const char *state, char *action, char *type) {\n")
#     out.write("  printf(\"{\\\"scenario\\\":\\\"%s\\\", \\\"state\\\":\\\"%s\\\", \\\"" + \
#         "action\\\":\\\"%s\\\", \\\"type\\\":\\\"%s\\\"}\", scen, state, action, type);")
#     out.write("\n}\n\n")
#     out.close()

def outputToTemplate(symbolTable, allFSMs, filename, helper):
    env = Environment(loader=FileSystemLoader('./'), extensions=['jinja2.ext.do'])

    out_h = open(os.path.splitext(filename)[0] + '_mon.h', 'w')
    template_h = env.get_template('templates/object_mon.h')
    obj = symbolTable.getSymbolsByType('object')[0]
    state_vars = [{'type':symbolTable.get(v)['datatype'], 'name':v} for v in symbolTable.getSymbolsByType('state')]
    for s in state_vars:
        s['c_type'] = convertTypeForC(s['type'])  
    identities = [{'type':symbolTable.get(v)['datatype'], 'name':v} for v in symbolTable.getSymbolsByType('identity')]
    for id in identities:
        id['c_type'] = convertTypeForC(id['type'])
    values = dict()
    values['multithreaded'] = True #command line arg for this?
    values['identities'] = identities
    values['obj'] = obj
    values['identities'] = identities
    values['state_vars'] = state_vars
    values['state_var_declarations'] = '\n'.join(['  %s %s;'%(v['c_type'], v['name']) for v in state_vars])
    values['identity_declarations'] = '\n'.join(['  %s %s;'%(v['c_type'], v['name']) for v in identities])
    values['scenario_names'] = [('%s_%s'%(obj, k)).upper() for k in allFSMs.keys()]

    out_c = open(os.path.splitext(filename)[0] + '_mon.c', 'w')
    template_c = env.get_template('templates/object_mon.c')
    values['helper'] = helper

    values['base_file_name'] = os.path.splitext(os.path.basename(filename))[0]
    values['identities_names'] = ['%s_%s'%(obj.upper(), i['name'].upper()) for i in identities]
    values['identities_types'] = [i['type'].upper() for i in identities]
  
    statesets = collections.OrderedDict()
    state_enums = []
    state_names_arrays = []
    state_inits = []
    for key, fsm in allFSMs.iteritems():
        stateset = [("%s_%s_%s" % (obj, key, state)).upper() for state in fsm.states.keys()]
        statesets[key] = stateset
        stateset_str = ", ".join(stateset)
        state_enums.append('typedef enum { ' + stateset_str + ' } %s_%s_state;'%(obj.lower(), key.lower()))
        state_names = ", ".join(['\"%s\"'%(state) for state in fsm.states.keys()])
        state_names_arrays.append('const char *%s_%s_states[%d] = {%s};'%(obj.lower(), key.lower(), len(fsm.states.keys()), state_names))
        state_inits.append('    monitor->state[%s_%s] = %s;'%(obj.upper(), key.upper(), stateset[0]))
    values['state_enums'] = '\n'.join(state_enums)
    values['state_names'] = '\n'.join(state_names_arrays)
    values['state_names_array'] = ['%s_%s_states'%(obj.lower(), key.lower()) for key in allFSMs.keys()]
    values['state_inits'] = '\n'.join(state_inits)

    events = ['%s_%s'%(obj.upper(), str(e).upper()) for e in symbolTable.getEvents()]
    values['event_enums'] = ', '.join(events)
    errors = ['%s_DEFAULT'%obj.upper()]
    for e in symbolTable.getSymbolsByType('event'):
        if symbolTable[e]['error']:
            errors.append('%s_%s'%(obj.upper, e.upper()))
    values['error_enums'] = ', '.join(errors)

    values['add_to_map_calls'] = ['add_%s_monitor_to_map(monitor, %s)'%(obj.lower(), i) for i in values['identities_names']]

    # Output a method for each event (switch statement to handle FSM transitions)
    methods = symbolTable.getEvents()
    callCases = []
    values['signatures']= []
    values['event_code'] = list()
    for m in methods:
        eventFunction = list()
        params = symbolTable.get(m, 'params')
        if len(params) > 0:
            params = obj.title() + "MonitorRecord* monitor_list, " + params
        else:
            params = obj.title() + "MonitorRecord* monitor_list"
        signature = 'void %s_%s(%s)' % (obj.lower(), m, params)
        values['signatures'].append(signature)
        eventFunction.append(signature + ' {')
        eventFunction.append('  %sMonitorRecord *current = monitor_list;' % obj.title())
        eventFunction.append('  while(current != NULL) {')
        eventFunction.append('    %sMonitor* monitor = current->monitor;' % obj.title())
        for key, fsm in allFSMs.iteritems():
            reference = 'monitor->state[%s_%s]' % (obj.upper(), key.upper())
            name_reference = "%s_states_names[%s_%s][monitor->state[%s_%s]]"%(obj.lower(), obj.upper(), key.upper(), obj.upper(), key.upper())
            eventFunction.append('    switch (%s) {' % reference)
            for transition in fsm.getTransitionsByEvent(str(m)):
                eventFunction.append(writeCaseTransition(obj, transition, reference, name_reference, key, m))
            eventFunction.append('      default:')
            eventFunction.append('        raise_error(\"%s_%s\", %s, \"%s\", \"DEFAULT\");'%(obj.lower(), key, name_reference, m))
            eventFunction.append('        break;')
            eventFunction.append('    }')
        eventFunction.append('    current = current->next;')
        eventFunction.append('  }')
        eventFunction.append('}')

        raiseFunction = writeRaiseFunction(symbolTable, m, obj)
        values['signatures'].append(raiseFunction['signature'])
        values['event_code'] .append({'event':eventFunction, 'raise':raiseFunction['code']})
        callCases.append(writeCallCase(symbolTable, m))

    # methods = symbolTable.getEvents()
    # callCases = []
    # values['event_code'] = list()
    # for m in methods:
    #     eventFunction = list()
    #     params = symbolTable.get(m, 'params')
    #     if len(params) > 0:
    #         params = obj.title() + "Monitor* monitor, " + params
    #     else:
    #         params = obj.title() + "Monitor* monitor"
    #     eventFunction.append('void ' + m + '(' + params + ') {')
    #     for key, fsm in allFSMs.iteritems():
    #         reference = 'monitor->state[%s_%s]' % (obj.upper(), key.upper())
    #         name_reference = "%s_states_names[%s_%s][monitor->state[%s_%s]]"%(obj.lower(), obj.upper(), key.upper(), obj.upper(), key.upper())
    #         eventFunction.append('  switch (%s) {' % reference)
    #         for transition in fsm.getTransitionsByEvent(str(m)):
    #             eventFunction.append(writeCaseTransition(obj, transition, reference, name_reference, key, m))
    #         eventFunction.append('    default:')
    #         eventFunction.append('      raise_error(\"%s_%s\", %s, \"%s\", \"DEFAULT\");'%(obj.lower(), key, name_reference, m))
    #         eventFunction.append('      break;')
    #         eventFunction.append('  }')
    #     eventFunction.append('}')

    #     raiseFunction = writeRaiseFunction(symbolTable, m, obj)
    #     values['event_code'] .append({'event':eventFunction, 'raise':raiseFunction})
    #     callCases.append(writeCallCase(symbolTable, m))

    out_h.write(template_h.render(values))
    out_c.write(template_c.render(values))

    shutil.copyfile('./templates/actions.h', os.path.dirname(filename) + '/actions.h')
    shutil.copyfile('./templates/actions.c', os.path.dirname(filename) + '/actions.c')
    shutil.copyfile('./templates/monitor_map.h', os.path.dirname(filename) + '/monitor_map.h')
    shutil.copyfile('./templates/monitor_map.c', os.path.dirname(filename) + '/monitor_map.c')

def convertTypeForC(smedlType):
    return {
        'int': 'int',
        'pointer': 'void*',
        'thread': 'pthread_t',
        'opaque': 'void*'
    }[smedlType]

def writeCaseTransition(obj, trans, currentState, stateName, scenario, action):
    output = ['      case %s_%s_%s:\n' % (obj.upper(), scenario.upper(), trans.startState.name.upper())]
    if trans.guard:
        output.append('        if(' + trans.guard.replace('this.', 'monitor->').replace('this', 'monitor') + ') {\n')
        output.append('          %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, trans.nextState.name)).upper() + ';\n')
        output.append('        } else {\n')
        if trans.elseState:
            output.append('          %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, trans.elseState.name)).upper() + ';\n')
        else:
            output.append('          raise_error(\"%s\", %s, \"%s\", \"DEFAULT\");\n' % (scenario, stateName, action))
        output.append('        }\n')
    else:
        output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, trans.nextState.name)).upper() + ';\n')
    output.append('        break;\n')
    return "".join(output)


def getEventParams(paramString):
    paramsList = []
    params = [str(s) for s in paramString.split(', ')]
    for p in params:
        paramsList.append([str(s) for s in p.split(' ')])
    return paramsList


def writeCallCase(symbolTable, event):
    output = []
    output.append('    case %s: ;'%event.upper())
    paramString = str(symbolTable.get(event)['params'])
    if paramString == '':
        output.append('      %s(monitor);'%event)
    else:
        params = getEventParams(paramString)
        for p in params:
            output.append('      %s %s_%s = monitor->action_queue->params->%c;'%(p[0], p[1], event, p[0][0]))
            output.append('      pop_param(&monitor->action_queue->params);')
        callParams = ", ".join('%s_%s'%(p[1], event) for p in params)
        output.append('      %s(%s);'%(event, ", ".join(['monitor', callParams])))
    output.append('      break;')
    return '\n'.join(output)


def writeRaiseFunction(symbolTable, event, obj):
    paramString = symbolTable.get(event, 'params')
    if len(paramString) > 0:
        paramString = obj.title() + "Monitor* monitor, " + paramString
    else:
        paramString = obj.title() + "Monitor* monitor"
    output = []
    signature = 'void raise_%s_%s(%s)' % (obj.lower(), event, paramString)
    output.append(signature + ' {')
    output.append('  param *p_head = NULL;')
    if len(paramString) > 0:
        for p in getEventParams(paramString):
            if p[0] == 'int':
                output.append('  push_param(&p_head, &%s, NULL, NULL, NULL);'%p[1])
            elif p[0] == 'char':
                output.append('  push_param(&p_head, NULL, &%s, NULL, NULL);'%p[1])
            elif p[0] == 'double':
                output.append('  push_param(&p_head, NULL, NULL, &%s, NULL);'%p[1])
            elif p[0] == 'pointer':
                output.append('  push_param(&p_head, NULL, NULL, NULL, &%s);'%p[1])
    output.append('  push_action(&monitor->action_queue, %s_%s, p_head);' % (obj.upper(), event.upper()))
    output.append('}\n\n')
    return {'code':output, 'signature':signature}


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
    if types is None: #probably never raised - called only for events in symbolTable
        raise ValueError("Unrecognized function, %s, found in scenarios" % function)
    if len(names) != len(types):
        raise ValueError("Invalid number of parameters for %s" % function)
    return (", ".join(["%s %s" % (types[i], names[i]) for i in range(len(names))]))


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
    # guard = checkReferences(guard) #TODO--------
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
                return "!(%s)" % guardToString(v)
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
                return (" %s " % object['operator']).join(comps)
            elif k == 'index':
                return "[%s]" % guardToString(v)
            elif k == 'params':
                if isinstance(v, list):
                    return "(%s)" % (", ".join([guardToString(val) for val in v]))
                else:
                    return "(%s)" % guardToString(v)
            elif k == 'dot':
                trailer = ""
                if object['trailer']:
                    trailer = guardToString(object['trailer'])
                return ".%s%s" % (v, trailer)
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
        atom = term.get('atom') or ""
        term_text = "%s%s" % (unary, atom)
        trailer_ast = term.get('trailer')
        if isinstance(trailer_ast, AST):
            for k, v in term.iteritems():
                term_text = "%s%s" % (term_text, guardToString(v) or "")
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


def checkReferences(guard):
    objects = re.findall(r'\s([A-Za-z_]\w*).\w+\W+', guard)


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description="Code Generator for SMEDL and PEDL.")
    parser.add_argument('-helper', '--helper', help='Header file for helper functions')
    parser.add_argument('pedl', metavar="PEDL", help="the PEDL file to parse")
    parser.add_argument('smedl', metavar="SMEDL", help="the SMEDL file to parse")
    args = parser.parse_args()

    main(args.pedl, args.smedl, helper=args.helper)
