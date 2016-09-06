import re, os, collections
from jinja2 import Environment, PackageLoader
from smedl.mgen import MonitorGenerator

class CTemplater(object):
    @staticmethod
    def output(mgen, allFSMs, filename, helper, pedlAST):
        if mgen._debug:
            if pedlAST:
                print("Target Monitor Points: " + pedlAST.getTargetMonitorPoints())
        obj = mgen._symbolTable.getSymbolsByType('object')[0]
        state_vars = [{'type': mgen._symbolTable.get(v)['datatype'], 'name': v} for v in mgen._symbolTable.getSymbolsByType('state')]
        for s in state_vars:
            s['c_type'] = CTemplater.convertTypeForC(s['type'])

        # If there are no identities defined, make a default one:
        if len(mgen._symbolTable.getSymbolsByType('identity')) == 0:
            identities = [{'type': 'opaque', 'name': 'id'}]
        else:
            identities = [{'type': mgen._symbolTable.get(v)['datatype'], 'name': v} for v in mgen._symbolTable.getSymbolsByType('identity')]
        for id in identities:
            id['c_type'] = CTemplater.convertTypeForC(id['type'])

        values = dict()
        values['multithreaded'] = True # command line arg for this?
        values['identities'] = identities
        values['obj'] = obj
        values['state_vars'] = state_vars
        values['state_var_declarations'] = '\n'.join(['  %s %s;' % (v['c_type'], v['name']) for v in state_vars])
        values['identity_declarations'] = '\n'.join(['  %s %s;' % (v['c_type'], v['name']) for v in identities])
        values['scenario_names'] = [('%s_%s_SCENARIO' % (obj, k)).upper() for k in list(allFSMs.keys())]
        values['helper'] = helper
        values['base_file_name'] = os.path.splitext(os.path.basename(filename))[0]
        values['identities_names'] = ['%s_%s' % (obj.upper(), i['name'].upper()) for i in identities]
        values['identities_types'] = [i['type'].upper() for i in identities]

        statesets = collections.OrderedDict()
        state_enums = []
        state_names_arrays = []
        state_inits = []
        for key, fsm in list(allFSMs.items()):
            stateset = []
            for state in list(fsm.states.keys()):
                st = ("%s_%s_%s" % (obj, key, state)).upper()
                if fsm.getStateByName(state) == fsm.startState:
                    startstate = st
                stateset.append(st)
            sorted(stateset)
            statesets[key] = stateset
            stateset_str = ", ".join(stateset)
            state_enums.append('typedef enum { ' + stateset_str + ' } %s_%s_state;' % (obj.lower(), key.lower()))
            state_names = ", ".join(['\"%s\"'%(state) for state in list(fsm.states.keys())])
            state_names_arrays.append('const char *%s_%s_states[%d] = { %s };' % (obj.lower(), key.lower(), len(list(fsm.states.keys())), state_names))
            state_inits.append('    monitor->state[%s_%s_SCENARIO] = %s;' % (obj.upper(), key.upper(), startstate))
        values['state_enums'] = '\n'.join(state_enums)
        values['state_names'] = '\n'.join(state_names_arrays)
        values['state_names_array'] = ['%s_%s_states' % (obj.lower(), key.lower()) for key in list(allFSMs.keys())]
        values['state_inits'] = '\n'.join(state_inits)

        events = ['%s_%s_EVENT' % (obj.upper(), str(e).upper()) for e in mgen._symbolTable.getEvents()]
        values['event_enums'] = ', '.join(events)
        errors = ['%s_DEFAULT' % obj.upper()]
        for e in mgen._symbolTable.getSymbolsByType('event'):
            if mgen._symbolTable[e]['error']:
                errors.append('%s_%s_EVENT' % (obj.upper, e.upper()))
        values['error_enums'] = ', '.join(errors)

        values['add_to_map_calls'] = ['add_%s_monitor_to_map(monitor, %s)' % (obj.lower(), i) for i in values['identities_names']]

        # Output a method for each event (switch statement to handle FSM transitions)
        methods = mgen._symbolTable.getEvents()
        callCases = []
        values['signatures']= []
        values['event_code'] = []
        values['event_msg_handlers'] = []
        values['bindingkeys_num'] = 1 # TODO: Make these customizable
        values['bindingkeys_str'] = '"#"'

        for m in methods:
            eventFunction = []
            probeFunction = []
            params = ''
            identityParams = []
            pedlEvent = False
            if 'imported_events' == mgen._symbolTable.get(m)['type'] and pedlAST is not None:
                for e in pedlAST.event_defs:
                    if str(m) == e.event:
                        pedlEvent = True
                        # TODO: parse identities in PEDL events
                        #if e.when:
                            #name = e.when['comp'][0]['atom']
                            #datatype = self._symbolTable.get(name)['datatype']
                            #c_type = self._convertTypeForC(datatype)
                            #identityParams.append({'name': name, 'c_type': c_type, 'datatype': datatype})
                            #print('%s pedl params: %s %s'%(m, c_type, name))

            if mgen._debug:
                print(m)
                print(mgen._symbolTable.get(m, 'params'))

            monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                [{'name': p['name'], 'c_type': CTemplater.convertTypeForC(p['type'])} for p in mgen._symbolTable.get(m, 'params')]

            if 'exported_events' != mgen._symbolTable.get(m)['type']:
                eventSignature = 'void %s_%s(%s)' % (obj.lower(), m, ", ".join(['%s %s'%(p['c_type'], p['name']) for p in monitorParams]))
                values['signatures'].append(eventSignature)
                eventFunction.append(eventSignature + ' {')
                for key, fsm in allFSMs.items():
                    trans_group = fsm.groupTransitionsByStartState(fsm.getTransitionsByEvent(str(m)))

                    # Jump to next FSM if this one contains no transitions for the current event
                    if len(trans_group) == 0:
                        continue

                    reference = 'monitor->state[%s_%s_SCENARIO]' % (obj.upper(), key.upper())
                    name_reference = "%s_states_names[%s_%s_SCENARIO][monitor->state[%s_%s_SCENARIO]]"%(obj.lower(), obj.upper(), key.upper(), obj.upper(), key.upper())
                    eventFunction.append('  switch (%s) {' % reference)
                    for start_state, transitions in trans_group.items():
                        eventFunction.append(CTemplater._writeCaseTransition(mgen, obj, transitions, reference, name_reference, key))
                    if mgen._implicitErrors:
                        eventFunction.append('    default:')
                        eventFunction.append('      raise_error(\"%s_%s\", %s, \"%s\", \"DEFAULT\");' % (obj.lower(), key, name_reference, m))
                        eventFunction.append('      break;')
                    eventFunction.append('  }')
                eventFunction.append('}')

                # Build event message handler block for incoming RabbitMQ messages
                msg_handler = []
                if len(values['event_msg_handlers']) == 0:
                    cond = 'if'
                else:
                    cond = '                else if'
                msg_handler.append(cond + ' (!strcmp(eventName,"%s_%s")) {' % (obj.lower(), m))
                sscanfStr = '%s'
                sscanfAttrs = 'e'
                retAttrs = ''
                for p in monitorParams[1:]:
                    msg_handler.append('                    %s %s = 0;' % (p['c_type'], p['name']))
                    if p['c_type'] == 'int':
                        sscanfStr += ' %d'
                    elif p['c_type'] == 'char':
                        sscanfStr += ' %s'
                    elif p['c_type'] == 'float':
                        exit("this should never happen. there is a missing float->double conversion.")
                    elif p['c_type'] == 'double':
                        sscanfStr += ' %lf'
                    sscanfAttrs += ', &' + p['name']
                    retAttrs += ', ' + p['name']
                msg_handler.append('                    int ret = sscanf(string, "' + sscanfStr + '", ' + sscanfAttrs + ');')
                msg_handler.append('                    if (ret == ' + str(len(monitorParams)) + ') {')
                msg_handler.append('                        ' + obj.lower() + '_' + m + '(monitor' + retAttrs + ');')
                msg_handler.append('                        printf("%s_%s called.\\n");' % (obj.lower(), m))
                msg_handler.append('                    }')
                msg_handler.append('                }')
                values['event_msg_handlers'].append('\n'.join(msg_handler))

            raiseFunction = CTemplater._writeRaiseFunction(mgen, m, obj)

            # Build the event handler function
            if pedlEvent:
                probeParams = [p for p in monitorParams if p['name'] != 'monitor']
                probeSignature = 'void %s_%s_probe(%s%s)' % (obj.lower(), m, ", ".join(['%s %s'%(p['c_type'], p['name']) for p in identityParams]), ", ".join(['%s %s'%(p['c_type'], p['name']) for p in probeParams]))
                probeFunction.append(probeSignature  + ' {')
                if len(identityParams) > 0:
                    # Write function call to hash on the first identity we're searching for
                    identityEnum = '%s_%s' % (obj.upper(), identityParams[0]['name'].upper())
                    identityDatatype = identityParams[0]['datatype'].upper()
                    identityName = identityParams[0]['name'].lower()
                    if identityDatatype == 'INT':
                        identityName = '&' + identityName
                    probeFunction.append('  %sMonitorRecord* results = get_%s_monitors_by_identity(%s, %s, %s);'  \
                        % (obj.title(), obj.lower(), identityEnum, identityDatatype, identityName))
                    # Write function calls to further filter the list based on other identities we're searching for
                    for i in range(1, len(identityParams)):
                        identityEnum = '%s_%s' % (obj.upper(), identityParams[i]['name'].upper())
                        identityDatatype = identityParams[i]['datatype'].upper()
                        identityName = identityParams[i]['name'].lower()
                        if identityDatatype == 'INT':
                            identityName = '&' + identityName
                        probeFunction.append('  results = filter_%s_monitors_by_identity(results, %s, %s);' % (obj.lower(), identityEnum, identityName))
                else:
                    probeFunction.append('  %sMonitorRecord* results = get_%s_monitors();' % (obj.title(), obj.lower()))
                probeFunction.append('  while(results != NULL) {')
                probeFunction.append('    %sMonitor* monitor = results->monitor;' % obj.title())
                probeFunction.append('    %s_%s(%s);' % (obj.lower(), m, ", ".join([p['name'] for p in monitorParams])))
                probeFunction.append('    results = results->next;')
                probeFunction.append('  }')
                probeFunction.append('}')
                values['signatures'].append(probeSignature)
                values['event_code'].append(CTemplater._updateVarNames(mgen, {'event':eventFunction, 'probe':probeFunction, 'raise':raiseFunction['code']}, m))
            else:
                values['event_code'].append(CTemplater._updateVarNames(mgen, {'event':eventFunction, 'raise':raiseFunction['code']}, m))

            values['signatures'].append(raiseFunction['signature'])

            callCases.append(CTemplater._writeCallCase(mgen, m))

        # Render the monitor templates and write to disk
        env = Environment(loader=PackageLoader('smedl.c_style','.'))

        out_h = open(os.path.splitext(filename)[0] + '_mon.h', 'w')
        out_h.write(env.get_template('object_mon.h').render(values))
        out_h.close()

        out_c = open(os.path.splitext(filename)[0] + '_mon.c', 'w')
        out_c.write(env.get_template('object_mon.c').render(values))
        out_c.close()

        # Copy pre-written static helper files to the output path
        a_h = open(os.path.dirname(filename) + '/actions.h', 'w')
        a_h.write(env.get_template('actions.h').render())
        a_h.close()

        a_c = open(os.path.dirname(filename) + '/actions.c', 'w')
        a_c.write(env.get_template('actions.c').render())
        a_c.close()

        m_h = open(os.path.dirname(filename) + '/monitor_map.h', 'w')
        m_h.write(env.get_template('monitor_map.h').render())
        m_h.close()

        m_c = open(os.path.dirname(filename) + '/monitor_map.c', 'w')
        m_c.write(env.get_template('monitor_map.c').render())
        m_c.close()


    # Translate a SMEDL type to a C type
    def convertTypeForC(smedlType):
        typeMap =  {
            'int': 'int',
            'float': 'double',
            'double': 'double',
            'pointer': 'void*',
            'thread': 'pthread_t',
            'opaque': 'void*'
        }
        if smedlType in typeMap:
            return typeMap[smedlType]
        else:
            return smedlType


    def _updateVarNames(mgen, funcs, method):
        out = {}
        for name, func in funcs.items():
            tmp = func
            for p in mgen._symbolTable.get(method, 'params'):
                out_s = []
                for s in tmp:
                    out_s.append(re.sub(r'\b' + p['true_name'] + r'\b', p['name'], s))
                tmp = out_s
            out[name] = tmp
        return out


    # Write out the switch statement case for a SMEDL trace transition
    def _writeCaseTransition(mgen, obj, transitions, currentState, stateName, scenario):
        output = ['    case %s_%s_%s:\n' % (obj.upper(), scenario.upper(), transitions[0].startState.name.upper())]

        if mgen._debug:
            print("\n*** Write Case Transition ***")
            print("Object: %s" % obj)
            for t in transitions:
                print("Transition: %s" % t)
            print("Current State: ", currentState)
            print("State Name: ", stateName)
            print("Scenario: ", scenario)
            print("\n")

        sorted(transitions, key = lambda trans: trans.guard)
        for i in range(len(transitions)):
            if i == 0 and transitions[i].guard:
                output.append('      if(' + transitions[i].guard.replace('this.', 'monitor->') + ') {\n')
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mgen._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                output.append('      }\n')
            elif len(transitions) == 1:
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mgen._writeAction(obj, action))
                output.append('      %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                break
            elif transitions[i].guard:
                output.append('      else if(' + transitions[i].guard.replace('this.', 'monitor->') + ') {\n')
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mgen._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                output.append('      }\n')

            # Handle Else (an Else state is defined, or reaching an Else denotes an error condition)
            if transitions[i].elseState and ((i+1 < len(transitions) and transitions[i+1].guard is None) or i+1 == len(transitions)):
                output.append('      else {\n')
                if transitions[i].elseActions:
                    for action in transitions[i].elseActions:
                        output.append('        %s\n' % mgen._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].elseState.name)).upper() + ';\n')
                output.append('      }\n')
            elif mgen._implicitErrors and i == len(transitions)-1:
                output.append('      else {\n')
                output.append('        raise_error(\"%s\", %s, \"%s\", \"DEFAULT\");\n' % (scenario, stateName, currentState))
                output.append('      }\n')
        output.append('      break;\n')
        return "".join(output)


    def _writeCallCase(mgen, event):
        output = []
        output.append('    case %s: ;' % event.upper())
        paramString = ','.join(['%s %s'%(p['type'], p['name']) for p in mgen._symbolTable.get(event, 'params')])
        if paramString == '':
            output.append('      %s(monitor);' % event)
        else:
            params = MonitorGenerator._getEventParams(paramString)
            for p in params:
                output.append('      %s %s_%s = monitor->action_queue->params->%c;' % (p[0], p[1], event, p[0][0]))
                output.append('      pop_param(&monitor->action_queue->params);')
            callParams = ", ".join('%s_%s' % (p[1], event) for p in params)
            output.append('      %s(%s);' % (event, ", ".join(['monitor', callParams])))
        output.append('      break;')
        return '\n'.join(output)


    def _writeRaiseFunction(mgen, event, obj):
        paramString = ', '.join(['%s %s'%(CTemplater.convertTypeForC(p['type']), p['name']) for p in mgen._symbolTable.get(event, 'params')])
        if len(paramString) > 0:
            paramString = obj.title() + "Monitor* monitor, " + paramString
        else:
            paramString = obj.title() + "Monitor* monitor"
        output = []
        signature = 'void raise_%s_%s(%s)' % (obj.lower(), event, paramString)
        output.append(signature + ' {')
        output.append('  param *p_head = NULL;')
        if len(paramString) > 0:
            for p in MonitorGenerator._getEventParams(paramString):
                # comparing SMEDL types not C types.
                if p[0] == 'int':
                    output.append('  push_param(&p_head, &%s, NULL, NULL, NULL);' % p[1])
                elif p[0] == 'char':
                    output.append('  push_param(&p_head, NULL, &%s, NULL, NULL);' % p[1])
                elif p[0] == 'float':
                    exit("this should never happen. there is a missing float->double conversion.")
                elif p[0] == 'double':
                    output.append('  push_param(&p_head, NULL, NULL, &%s, NULL);' % p[1])
                elif p[0] == 'pointer':
                    output.append('  push_param(&p_head, NULL, NULL, NULL, &%s);' % p[1])
        output.append('  push_action(&monitor->action_queue, %s_%s_EVENT, p_head);' % (obj.upper(), event.upper()))

        if 'exported_events' == mgen._symbolTable.get(event)['type']:
            output.append('  char message[256];')
            sprintf = '  sprintf(message, "%s_%s' % (obj.lower(), event)
            evParams = MonitorGenerator._getEventParams(paramString)[1:]
            if len(evParams) > 0:
                for p in evParams:
                    # comparing SMEDL types not C types.
                    if p[0] == 'int':
                        sprintf += ' %d'
                    elif p[0] == 'char':
                        sprintf += ' %s'
                    elif p[0] == 'double':
                        sprintf += ' %lf'
                    elif p[0] == 'float':
                        exit("this should never happen. there is a missing float->double conversion.")
            sprintf += '"'
            if len(evParams) > 0:
                for p in evParams:
                    sprintf += ', %s' % p[1]
            sprintf += ');'
            output.append(sprintf)
            output.append('  char routing_key[256];')

            sprintf_routing = '  sprintf(routing_key, "%s-%s_%s.' % (obj.lower(), obj.lower(), event)
            # TODO: peter, write functions for printing and parsing monitor identities
            # this cast is broken and wrong, but works as long as we have only one monitor process
            sprintf_routing += '%ld", (long)monitor->identities['
            sprintf_routing += '%s_ID]);' % obj.upper() # TODO: Update this value with exact identity name defined in SMEDL
            output.append(sprintf_routing)
            output.append('  send_message(monitor, message, routing_key);')
        output.append('}\n\n')
        return {'code':output, 'signature':signature}
