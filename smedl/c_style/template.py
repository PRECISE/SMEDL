import re, os, collections
from jinja2 import Environment, PackageLoader
from .. import mgen

class CTemplater(object):
    @staticmethod
    def output(mg, allFSMs, filename, helper, pedlAST):
        if mg._debug:
            if pedlAST:
                print("Target Monitor Points: " + pedlAST.getTargetMonitorPoints())
        obj = mg._symbolTable.getSymbolsByType('object')[0]
        state_vars = [{'type': mg._symbolTable.get(v)['datatype'], 'name': v} for v in mg._symbolTable.getSymbolsByType('state')]
        for s in state_vars:
            s['c_type'] = CTemplater.convertTypeForC(s['type'])

        # If there are no identities defined, make a default one:
        if len(mg._symbolTable.getSymbolsByType('identity')) == 0:
            identities = [{'type': 'opaque', 'name': 'id'}]
        else:
            identities = [{'type': mg._symbolTable.get(v)['datatype'], 'name': v} for v in mg._symbolTable.getSymbolsByType('identity')]
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

        events = ['%s_%s_EVENT' % (obj.upper(), str(e).upper()) for e in mg._symbolTable.getEvents()]
        values['event_enums'] = ', '.join(events)
        errors = ['%s_DEFAULT' % obj.upper()]
        for e in mg._symbolTable.getSymbolsByType('event'):
            if mg._symbolTable[e]['error']:
                errors.append('%s_%s_EVENT' % (obj.upper, e.upper()))
        values['error_enums'] = ', '.join(errors)

        values['add_to_map_calls'] = ['add_%s_monitor_to_map(monitor, %s)' % (obj.lower(), i) for i in values['identities_names']]

        # Output a method for each event (switch statement to handle FSM transitions)
        methods = mg._symbolTable.getEvents()
        callCases = []
        values['signatures']= []
        values['event_code'] = []
        values['event_msg_handlers'] = []
        if mg._getBindingKeysNum() == 0:
            values['bindingkeys_num'] = 1 # TODO: Make these customizable
        else:
            values['bindingkeys_num'] = mg._getBindingKeysNum()# TODO: Make these customizable

        values['b_keys'] = CTemplater._getBindingKeys(mg)

        #construct event_msg_handlers
        #msg_handler = []
        name = mg._symbolTable.getSymbolsByType('object')[0]
        for conn in mg.archSpec:
            if conn.targetMachine == name:
                monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                [{'name': p['name'], 'c_type': CTemplater.convertTypeForC(p['type'])} for p in mg._symbolTable.get(conn.targetEvent, 'params')]
                msg_handler = []
                if len(values['event_msg_handlers']) == 0:
                    cond = 'if'
                else:
                    cond = '                else if'

                msg_handler.append(cond + ' (!strcmp(eventName,"%s")) {' % conn.connName)

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
                msg_handler.append('                        ' + obj.lower() + '_' + conn.targetEvent + '(monitor' + retAttrs + ');')
                msg_handler.append('                        printf("%s_%s called.\\n");' % (obj.lower(), conn.targetEvent))
                msg_handler.append('                    }')
                msg_handler.append('                }')

                values['event_msg_handlers'].append('\n'.join(msg_handler))

        for m in methods:
            eventFunction = []
            probeFunction = []
            params = ''
            identityParams = []
            pedlEvent = False
            if 'imported_events' == mg._symbolTable.get(m)['type'] and pedlAST is not None:
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

            if mg._debug:
                print(m)
                print(mg._symbolTable.get(m, 'params'))

            monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                [{'name': p['name'], 'c_type': CTemplater.convertTypeForC(p['type'])} for p in mg._symbolTable.get(m, 'params')]

            if 'exported_events' != mg._symbolTable.get(m)['type']:
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
                        eventFunction.append(CTemplater._writeCaseTransition(mg, obj, transitions, reference, name_reference, key))
                    if mg._implicitErrors:
                        eventFunction.append('    default:')
                        eventFunction.append('      raise_error(\"%s_%s\", %s, \"%s\", \"DEFAULT\");' % (obj.lower(), key, name_reference, m))
                        eventFunction.append('      break;')
                    eventFunction.append('  }')
                eventFunction.append('}')



            raiseFunction = CTemplater._writeRaiseFunction(mg, m, obj)

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
                values['event_code'].append(CTemplater._updateVarNames(mg, {'event':eventFunction, 'probe':probeFunction, 'raise':raiseFunction['code']}, m))
            else:
                values['event_code'].append(CTemplater._updateVarNames(mg, {'event':eventFunction, 'raise':raiseFunction['code']}, m))

            values['signatures'].append(raiseFunction['signature'])

            callCases.append(CTemplater._writeCallCase(mg, m))

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

    def _getBindingKeys(mg):
        lst = []
        name = mg._symbolTable.getSymbolsByType('object')[0]
        #print(name)
        k = 0
        for conn in mg.archSpec:
            b_str = 'bindingkeys['+str(k)+']'
            if name==conn.targetMachine:

                p_str = b_str + '=(char*)malloc(255*sizeof(char));\n'+'\tstrcpy('+b_str+',"'+conn.connName+'");\n'
                sourceMachine = mg._getMachine(conn.sourceMachine)
                if sourceMachine == None:
                    raise ValueError('source machine not exist')
                sourceEvent = mg._getSourceEvent(conn.sourceMachine,conn.sourceEvent)
                if sourceEvent == None:
                    raise ValueError('source event not exist')
                if conn.patternSpec == [] or conn.patternSpec == None:
                    lst.append(p_str+'strcat('+b_str+',".#");\n')
                else:
                    machineIndexDic = {}
                    eventIndexDic = {}
                    #TODO: generate predicates on the machine and event, add corresponding filter, for each target event, union all predicates
                    for p_spec in conn.patternSpec:
                        leftterm = p_spec.getLeftTerm()
                        rightterm = p_spec.getRightTerm()
                        if leftterm == rightterm or (not leftterm == conn.targetMachine and not rightterm == conn.targetsMachine) or (leftterm == conn.targetEvent and not conn.sourceEvent == conn.targetEvent ) or (rightterm == conn.targetEvent and not conn.sourceEvent == conn.targetEvent ):
                            raise ValueError('pattern expression syntax error')
                        else:
                            leftindex = p_spec.getLeftIndex()
                            rightindex = p_spec.getRightIndex()
                            if mg._checkBound(conn,leftterm,leftindex) and mg._checkBound(conn,rightterm,rightindex):
                                if leftterm == conn.targetMachine:
                                    val = mg._getIdentityName(leftindex)
                                    if rightterm == conn.sourceEvent:
                                        eventIndexDic[rightindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                                    elif rightterm == conn.sourceMachine:
                                        machineIndexDic[rightindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                                elif rightterm == conn.targetMachine:
                                    #val = self._getIdentityName(rightindex)
                                    if leftterm == conn.sourceEvent:
                                        eventIndexDic[leftindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                                    elif leftterm == conn.sourceMachine:
                                        machineIndexDic[leftindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                            else:
                                raise ValueError('out of bound in pattern expression')
                    #build binding key and add it to lst
                    machineIndex = 0
                    eventIndex = 0

                    while machineIndex < len(sourceMachine.params):
                        if not machineIndex in machineIndexDic.keys():
                            p_str += '\tstrcat('+b_str+',".*");\n'
                        else:
                            p_str += '\tstrcat('+b_str+',".");\n'
                            p_str += '\tstrcat('+b_str+',itoa(*(int*)('+machineIndexDic[machineIndex]+'));\n'
                        machineIndex = machineIndex + 1

                    p_str +='\tstrcat('+b_str+',".'+sourceEvent.event_id+'");\n'
                    while eventIndex < len(sourceEvent.params):
                        if not eventIndex in eventIndexDic.keys():
                            p_str += '\tstrcat('+b_str+',".*");\n'
                        else:
                            p_str += '\tstrcat('+b_str+',".");\n'
                            p_str += '\tstrcat('+b_str+',itoa(*(int*)('+eventIndexDic[machineIndex]+')));\n'
                        eventIndex = eventIndex + 1
                    lst.append(p_str)
                    #print(p_str)
                    k = k + 1
        bindingkey = ''
        i = 0
        #print(lst)
        for s in lst:
            bindingkey += s
            i = i+1
        if len(lst)==0:
            bindingkey+='bindingkeys[0]=(char*)malloc(255*sizeof(char));\n'+'\tstrcpy(bindingkeys[0],"#");\n'
        return bindingkey

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


    def _updateVarNames(mg, funcs, method):
        out = {}
        for name, func in funcs.items():
            tmp = func
            for p in mg._symbolTable.get(method, 'params'):
                out_s = []
                for s in tmp:
                    out_s.append(re.sub(r'\b' + p['true_name'] + r'\b', p['name'], s))
                tmp = out_s
            out[name] = tmp
        return out


    # Write out the switch statement case for a SMEDL trace transition
    def _writeCaseTransition(mg, obj, transitions, currentState, stateName, scenario):
        output = ['    case %s_%s_%s:\n' % (obj.upper(), scenario.upper(), transitions[0].startState.name.upper())]

        if mg._debug:
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
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                output.append('      }\n')
            elif len(transitions) == 1:
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('      %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                break
            elif transitions[i].guard:
                output.append('      else if(' + transitions[i].guard.replace('this.', 'monitor->') + ') {\n')
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                output.append('      }\n')

            # Handle Else (an Else state is defined, or reaching an Else denotes an error condition)
            if transitions[i].elseState and ((i+1 < len(transitions) and transitions[i+1].guard is None) or i+1 == len(transitions)):
                output.append('      else {\n')
                if transitions[i].elseActions:
                    for action in transitions[i].elseActions:
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].elseState.name)).upper() + ';\n')
                output.append('      }\n')
            elif mg._implicitErrors and i == len(transitions)-1:
                output.append('      else {\n')
                output.append('        raise_error(\"%s\", %s, \"%s\", \"DEFAULT\");\n' % (scenario, stateName, currentState))
                output.append('      }\n')
        output.append('      break;\n')
        return "".join(output)


    def _writeCallCase(mg, event):
        output = []
        output.append('    case %s: ;' % event.upper())
        paramString = ','.join(['%s %s'%(p['type'], p['name']) for p in mg._symbolTable.get(event, 'params')])
        if paramString == '':
            output.append('      %s(monitor);' % event)
        else:
            params = mgen.MonitorGenerator._getEventParams(paramString)
            for p in params:
                output.append('      %s %s_%s = monitor->action_queue->params->%c;' % (p[0], p[1], event, p[0][0]))
                output.append('      pop_param(&monitor->action_queue->params);')
            callParams = ", ".join('%s_%s' % (p[1], event) for p in params)
            output.append('      %s(%s);' % (event, ", ".join(['monitor', callParams])))
        output.append('      break;')
        return '\n'.join(output)


    def _writeRaiseFunction(mg, event, obj):
        paramString = ', '.join(['%s %s'%(CTemplater.convertTypeForC(p['type']), p['name']) for p in mg._symbolTable.get(event, 'params')])
        if len(paramString) > 0:
            paramString = obj.title() + "Monitor* monitor, " + paramString
        else:
            paramString = obj.title() + "Monitor* monitor"
        output = []
        signature = 'void raise_%s_%s(%s)' % (obj.lower(), event, paramString)
        output.append(signature + ' {')
        output.append('  param *p_head = NULL;')
        if len(paramString) > 0:
            for p in mgen.MonitorGenerator._getEventParams(paramString):
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

        if 'exported_events' == mg._symbolTable.get(event)['type']:
            output.append('  char message[256];')
            sprintf = '  sprintf(message, "%s_%s' % (obj.lower(), event)
            evParams = mgen.MonitorGenerator._getEventParams(paramString)[1:]
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

            #construct routing key
            name = mg._symbolTable.getSymbolsByType('object')[0]
            #print(name)
            connName = None
            #print(mg.archSpec)
            for conn in mg.archSpec:
                if conn.sourceMachine == name and conn.sourceEvent == event:
                    connName = conn.connName
                    break

                if connName == None:
                        connName = obj+'_'+ event
            sprintf_routing = '  sprintf(routing_key, "%s' % (connName)
            # TODO: peter, write functions for printing and parsing monitor identities
            # this cast is broken and wrong, but works as long as we have only one monitor process
            for v in mg.identities:
                sprintf_routing += '.%ld'

                sprintf_routing += '.'+event
                if len(evParams) > 0:
                    for p in evParams:
                        # attributes can only be int
                        if p[0] == 'int':
                            sprintf_routing += '.%d'
                        else:
                            sprintf_routing += '.0'

            sprintf_routing+='"'
            for v in mg.identities:
                sprintf_routing += ', (long)(*(int*)(monitor->identities['
                sprintf_routing += '%s_' % obj.upper() # TODO: Update this value with exact identity name defined in SMEDL
                sprintf_routing += v.upper() +']))'

            if len(evParams) > 0:
                for p in evParams:
                # attributes can only be int
                    if p[0] == 'int':
                        sprintf_routing+=', %s' % p[1]


            sprintf_routing += ');'
            output.append(sprintf_routing)
            output.append('  send_message(monitor, message, routing_key);')
        output.append('}\n\n')
        return {'code':output, 'signature':signature}
