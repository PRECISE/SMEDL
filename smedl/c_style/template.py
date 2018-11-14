import re, os, collections
from jinja2 import Environment, PackageLoader
import smedl.mgen
from smedl import __about__

class CTemplater(object):
    
    @staticmethod
    def _addDataString(st, state_vars):
        re = ''
        for s in state_vars:
            if s['default'] != None:
                v = s['default']
            else:
                v = 'NULL'
                if s['type'] == 'int' or s['type'] == 'float' or s['type'] == 'double':
                    v = '0'
                elif s['type'] == 'string' :
                    v = '\"0\"'
                #print(v)
            re += st + '->' + s['name'] + '=' + v + ';\n'
        return re



    @staticmethod
    def is_float_number(s):
        try:
            float(s)
            return True
        except ValueError:
            return False

    @staticmethod
    def is_int_number(s):
        try:
            int(s)
            return True
        except ValueError:
            return False

    @staticmethod
    def _checkDefaultAssign(state_vars):
        for s in state_vars:
            #print (s)
            if s['default'] == None:
                continue
            if s['type'] == 'int' or s['type'] == 'char':
                if not CTemplater.is_int_number(s['default']):
                    return False
            elif s['type'] == 'float' or s['type'] == 'double' :
                if not CTemplater.is_float_number(s['default']):
                    return False
            elif s['type'] == 'string' :
                if s['default'][0] != '\"' or s['default'][len(s['default'])-1] != '\"':
                    return False
            elif s['type'] == 'thread' or s['type'] == 'opaque' or s['type'] == 'pointer' :
                if  s['default'] != 'null':
                    return False
        return True

    @staticmethod
    def output(mg, allFSMs, filename, helper, pedlAST, console_output=False, output_dir=''):
        if mg._debug:
            if pedlAST:
                print("Target Monitor Points: " + pedlAST.getTargetMonitorPoints())
        obj = mg._symbolTable.getSymbolsByType('object')[0]
        state_vars = [{'type': mg._symbolTable.get(v)['datatype'], 'name': v, 'default': mg._symbolTable.get(v)['default']} for v in mg._symbolTable.getSymbolsByType('state')]
        #print (state_vars)
        for s in state_vars:
            s['c_type'] = CTemplater.convertTypeForC(s['type'])
        if not CTemplater._checkDefaultAssign (state_vars):
            exit("wrong type of default value")
        values = dict()

        # Use object name as default synchronous set name, but find the actual
        # synchronous set if there is one
        sync_set_name = obj
        sync_set_monitors = [obj]
        for k,v in mg.synchronousSets.items():
            if obj in v:
                sync_set_name = k
                sync_set_monitors = v
                break;
        values['sync_set_monitors'] = sync_set_monitors
        values['sync_set_name'] = sync_set_name
        values['sync_set_monitors_enum'] = ', '.join(
                [sync_set_name.upper() + '_' + m.upper() + '_MONITOR' for m in sync_set_monitors])

        # If there are no identities defined, make a default one:
        if len(mg._symbolTable.getSymbolsByType('identity')) == 0:
            identities = [{'type': 'opaque', 'name': 'id'}]
        else:
            identities = [{'type': mg._symbolTable.get(v)['datatype'], 'name': v} for v in mg._symbolTable.getSymbolsByType('identity')]
        for id in identities:
            id['c_type'] = CTemplater.convertTypeForC(id['type'])


        # Monitor initialization
        # If a monitor has no creation event, we assume that we must create it ourself
        # (Note: Prior to synchronous communication, this was determined by checking for identities)
        monitors_to_init = []
        for iface in mg.monitorInterface:
            if iface.id in sync_set_monitors:
                has_creation = False
                for ev in iface.importedEvents:
                    if not ev.creation == None:
                        has_creation = True
                if not has_creation:
                    monitors_to_init.append(iface.id)
        values['monitors_to_statically_init'] = monitors_to_init
        mon_init_str = []
        for ident in identities:
            if ident['type'] == 'int':
                #mon_init_str.append('d->%s=malloc(sizeof(int));' % ident['name'])
                #mon_init_str.append('*(d->%s) = 0;' % ident['name'])
                mon_init_str.append('d->%s = 0;' % ident['name'])
            else:
                #mon_init_str.append('d->%s=malloc(1);' % ident['name'])
                #mon_init_str.append("*(char *)(d->%s) = '\\0';" % ident['name'])
                mon_init_str.append('d->%s = "";' % ident['name'])
        mon_init_str.append(CTemplater._addDataString('d', state_vars))
        values['mon_init_str'] = '\n'.join(mon_init_str)


        values['msg_format_version'] = '\"'+__about__['msg_format_version']+'\"'
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

        # Construct array executed_sceanrios
        values['num_scenarios'] = len(allFSMs.keys())
        zeroString = ''
        for i in range(len(allFSMs.keys())):
            if i == 0:
                zeroString += '0'
            else:
                zeroString += ',0'
        values['zeros'] = zeroString

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
        #values['remove_calls'] = ['remove_%s_monitor_to_map(monitor, %s, )' % (obj.lower(), i) for i in values['identities_names']]
        # Output a method for each event (switch statement to handle FSM transitions)
        methods = mg._symbolTable.getEvents()
        callCases = []
        values['signatures']= []
        values['event_code'] = []
        event_msg_handlers = []
        values['var_declaration'] = []
        values['pending_event_case'] = []
        values['export_event_case'] = []
        values['imported_event_case'] = []
        values['exported_event_case'] = []
        values['exported_event_routes'] = []

        # Make a list of binding keys
        values['b_keys'] = CTemplater._getBindingKeys(mg, sync_set_monitors)
        values['bindingkeys_num'] = len(values['b_keys'])
        if values['bindingkeys_num'] == 0:
            values['bindingkeys_num'] = 1

        ### Local Wrapper #####################################################

        # Local wrapper imported event handlers
        name = mg._symbolTable.getSymbolsByType('object')[0]
        for conn in mg.archSpec:
            if conn.targetMachine == name:
                callstring = []
                callstring.append('printf("' + obj + ' local wrapper importing ' + conn.targetEvent + ' event\\n");')

                connSpec = conn.patternSpec

                if connSpec == None or len(connSpec) == 0: # Are there identities to match?
                    # No identities
                    callstring.append('record = get_%s_monitors();' % obj.lower())
                else:
                    # Yes there are identities
                    callstring.append('record = get_%s_monitors_by_identities(identity, type, values, size);' % obj.lower())
                    
                    # If this is a creation event, we need dynamic instantiation code
                    targetEvent = mg._getTargetEvent(conn.targetMachine,conn.targetEvent)
                    if targetEvent.creation != None:
                        callstring.append('if(record == NULL){')

                        t_machine = mg._getMachine(conn.targetMachine)
                        t_machine_params = t_machine.params
                        t_lengthIdentityList = len(t_machine_params)
                        tmp_str = 'int target_parameterTypes [%d] = {' % (t_lengthIdentityList)
                        i = 0
                        for t in t_machine_params:
                            if i == 0:
                                tmp_str += t.upper()
                            else:
                                tmp_str += ',' + t.upper()
                            i += 1
                        tmp_str += '};'
                        callstring.append(tmp_str)

                        callstring.append('record = (%sMonitorRecord *)malloc(sizeof(%sMonitorRecord));' %(obj.title(), obj.title()))
                        callstring.append('%sData *d = (%sData *)malloc(sizeof(%sData));' %(obj.title(),obj.title(),obj.title()))
                        j = 0
                        for v in identities:
                            callstring.append('if (target_parameterTypes[identity['+str(j)+']]==INT){')
                            callstring.append('\t d ->' + v['name'] + '=' + '*(int*)values[' + str(j) + '];}')
                            callstring.append('else if(target_parameterTypes[identity['+str(j)+']]==STRING) {\t d ->' + v['name'] + '=(void*)' + 'values[' + str(j)+ '];}')
                            callstring.append('else {\t d ->' + v['name'] + '= (void *)NULL;}')
                            j += 1
                        callstring.append(CTemplater._addDataString('d',state_vars))
                        callstring.append('%sMonitor* tempMon = init_%s_monitor(d);' % (obj.title(),obj.lower()))
                        callstring.append('record -> monitor = tempMon;')
                        callstring.append('record -> next = NULL;')
                        callstring.append('}\n\t')

                callstring.append('{')
                callstring.append(obj.title() + "MonitorRecord *tmp;")

                # Pull params out
                ki = 0
                kd = 0
                kv = 0
                kc = 0
                handler_call = obj.lower() + '_' + conn.targetEvent + '(record->monitor'
                for p in mg._symbolTable.get(conn.targetEvent, 'params'):
                    if p['type'] == 'int':
                        callstring.append('int i' + str(ki) + ' = params->i;')
                        handler_call += ', i' + str(ki)
                        ki += 1
                    elif p['type'] == 'char':
                        callstring.append('char c' + str(kc) + ' = params->c;')
                        handler_call += ', c' + str(kc)
                        kc += 1
                    elif p['type'] == 'double' or p['type'] == 'float':
                        callstring.append('double d' + str(kd) + ' = params->d;')
                        handler_call += ', d' + str(kd)
                        kd += 1
                    elif p['type'] == 'pointer' or key == 'opaque':
                        callstring.append('void *v' + str(kv) + ' = params->v;')
                        handler_call += ', v' + str(kv)
                        kv += 1
                    elif p['type'] == 'string':
                        callstring.append('char *v' + str(kv) + ' = params->v;')
                        handler_call += ', v' + str(kv)
                        kv += 1
                    callstring.append('params = params->next;')
                callstring.append('cJSON *pro = params->provenance;')
                handler_call += ', pro);'

                # Call event handlers
                callstring.append('while(record != NULL) {')
                callstring.append('printf("' + obj + ' local wrapper dispatching ' + conn.targetEvent + ' to a monitor\\n");')
                callstring.append(handler_call)
                callstring.append("tmp = record;")
                callstring.append('record = record->next;')
                callstring.append("free(tmp);")
                callstring.append('}')
                callstring.append('}')

                values['imported_event_case'].append({'event_enum':[obj.upper()+'_'+conn.targetEvent.upper()+'_EVENT:'],'callstring':'\n'.join(callstring)})

        # Local wrapper exported event handlers
        for m in methods:
            if 'exported_events' == mg._symbolTable.get(m)['type']:
                callstring = []
                callstring.append('{')

                ki = 0
                kd = 0
                kv = 0
                kc = 0
                handler_call = 'exported_' + obj.lower() + '_' + m + '(identities'
                for p in mg._symbolTable.get(m, 'params'):
                    if p['type'] == 'int':
                        callstring.append('int i' + str(ki) + ' = params->i;')
                        handler_call += ', i' + str(ki)
                        ki += 1
                    elif p['type'] == 'char':
                        callstring.append('char c' + str(kc) + ' = params->c;')
                        handler_call += ', c' + str(kc)
                        kc += 1
                    elif p['type'] == 'double' or p['type'] == 'float':
                        callstring.append('double d' + str(kd) + ' = params->d;')
                        handler_call += ', d' + str(kd)
                        kd += 1
                    elif p['type'] == 'pointer' or key == 'opaque':
                        callstring.append('void *v' + str(kv) + ' = params->v;')
                        handler_call += ', v' + str(kv)
                        kv += 1
                    elif p['type'] == 'string':
                        callstring.append('char *v' + str(kv) + ' = params->v;')
                        handler_call += ', v' + str(kv)
                        kv += 1
                    callstring.append('params = params->next;')
                callstring.append('cJSON *pro = params->provenance;')
                handler_call += ', pro);'
                callstring.append('pop_param(&p_head);')

                callstring.append(handler_call)
                callstring.append('}')
 
                values['exported_event_case'].append({'event_enum':[obj.upper()+'_'+m.upper()+'_EVENT:'],'callstring':'\n'.join(callstring)})

        ### Global Wrapper ####################################################

        # Cases for the global wrapper export_event function
        for m in mg.monitorInterface:
            if m.id in sync_set_monitors:
                exported_event_list = []
                for ev in m.exportedEvents:
                    ev_name = ev.event_id
                    route_synchronously = False
                    route_asynchronously = False

                    # Is this event the source of a channel?
                    for conn in mg.archSpec:
                        if conn.sourceMachine == m.id and conn.sourceEvent == ev_name:
                            # It is. Is the destination inside and/or outside the synchronous set?
                            if conn.targetMachine in sync_set_monitors:
                                route_synchronously = True
                            else:
                                route_asynchronously = True
                    # If we didn't find any channel matching the event, it's asynchronous.
                    if route_synchronously == False and route_asynchronously == False:
                        route_asynchronously = True

                    callstring = []
                    if route_synchronously:
                        callstring.append('push_global_action(&sync_queue, monitor_type, identities, event_id, params);')
                    if route_asynchronously:
                        callstring.append('push_global_action(&async_queue, monitor_type, identities, event_id, params);')

                    if callstring != []:
                        exported_event_list.append({'casename':m.id.upper() + "_" + ev_name.upper() + "_EVENT:",'callstring':'\n'.join(callstring)})
                if exported_event_list != []:
                    values['exported_event_routes'].append({'casename':sync_set_name.upper() + "_" + m.id.upper() + "_MONITOR:", 'events':exported_event_list})

        # Global wrapper JSON handling
        for conn in mg.archSpec:
            if conn.targetMachine in sync_set_monitors and conn.sourceMachine not in sync_set_monitors:
                event_msg_handlers.append('if (!strcmp(eventName, "%s")) {' % conn.connName)
                
                # Get parameters
                ev_params = None
                for iface in mg.monitorInterface:
                    if iface.id == conn.targetMachine:
                        for ev in iface.importedEvents:
                            if ev.event_id == conn.targetEvent:
                                # Gets a list of type strings
                                ev_params = ev.params
                ev_params_c = []
                for smedl_type in ev_params:
                    ev_params_c.append(CTemplater.convertTypeForC(smedl_type))

                idx = 1
                for c_type in ev_params_c:
                    if c_type == 'char*':
                        event_msg_handlers.append('char *var%d = NULL;' % (idx))
                    else:
                        event_msg_handlers.append('%s var%d = 0;' % (c_type, idx))
                    idx += 1
                if len(ev_params) > 0:
                    event_msg_handlers.append('cJSON * fmt = cJSON_GetObjectItem(root, "params");')
                    event_msg_handlers.append('if (fmt != NULL) {');
                idx = 1
                for c_type in ev_params_c:
                    if c_type == 'int' or c_type == 'char':
                        event_msg_handlers.append('if (cJSON_GetObjectItem(fmt,"v%d") != NULL) {' % (idx))
                        event_msg_handlers.append('var%d = cJSON_GetObjectItem(fmt,"v%d")->valueint;' % (idx, idx))
                    elif c_type == 'double':
                        event_msg_handlers.append('if (cJSON_GetObjectItem(fmt,"v%d") != NULL) {' % (idx))
                        event_msg_handlers.append('var%d = cJSON_GetObjectItem(fmt,"v%d")->valuedouble;' % (idx, idx))
                    elif c_type == 'char*':
                        event_msg_handlers.append('if (cJSON_GetObjectItem(fmt,"v%d") != NULL) {' % (idx))
                        event_msg_handlers.append('var%d = cJSON_GetObjectItem(fmt,"v%d")->valuestring;' % (idx, idx))
                    idx += 1

                # Create target identities (if we need to)
                connSpec = conn.patternSpec
                if connSpec == None or len(connSpec) == 0:
                    event_msg_handlers.append('int *identity = NULL;')
                    event_msg_handlers.append('void **values = NULL;')
                    type = "INT" # doesn't matter what we set here, it won't be used
                    idList = []
                else:
                    #monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                    #[{'name': p['name'], 'c_type': CTemplater.convertTypeForC(p['type']), 'type' : p['type']} for p in mg._symbolTable.get(conn.targetEvent, 'params')]
                    monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}]
                    for mon in mg.monitorInterface:
                        if mon.id == conn.targetMachine:
                            for ev in mon.importedEvents:
                                if ev.event_id == conn.targetEvent:
                                    k = 0
                                    for t in ev.params:
                                        monitorParams.append({'name': 'p' + str(k), 'c_type': CTemplater.convertTypeForC(t), 'type': t})
                    #[{'name': p['name'], 'c_type': CTemplater.convertTypeForC(p['type']), 'type' : p['type']} for p in mg._symbolTable.get(conn.targetEvent, 'params')]
                    t_machine = mg._getMachine(conn.targetMachine)
                    t_machine_params = t_machine.params
                    t_lengthIdentityList = len(t_machine_params)
                    tmp_str = 'int target_parameterTypes [%d] = {' % (t_lengthIdentityList)
                    i = 0
                    for t in t_machine_params:
                        if i == 0:
                            tmp_str += t.upper()
                        else:
                            tmp_str += ',' + t.upper()
                        i += 1
                    tmp_str += '};'
                    event_msg_handlers.append(tmp_str)

                    j = 0
                    idList = [] 
                    type = "" 
                    #print (pattern)
                    eventParaList = [] 
                    eventParaList_ = {} 
                    for pattern in connSpec: #operator is always equal, leftTerm is identity of target monitor
                        if pattern.leftTerm != conn.targetMachine:
                            #print (pattern.leftTerm)
                            #print (conn)
                            #print(pattern.leftTerm)
                            #print(conn)
                            exit("illegal pattern1")
                        #if s_machine_params == None or pattern.leftIndex >= len(s_machine_params) :
                        #    exit("illegal pattern2")
                        #print(connSpec)
                        #print(pattern)
                        if pattern.rightTerm == conn.sourceEvent:
                            eventParaList.append(pattern.leftIndex)
                            eventParaList_[pattern.leftIndex]=pattern.rightIndex
                        if j == 0:
                            type = t_machine_params[pattern.leftIndex].upper()
                            j = 1
                        idList.append(pattern.leftIndex)

                    tmp_str = 'int identity[%d] = {' % len(connSpec)
                    j = 0
                    for i in idList:
                        if j == 0:
                            tmp_str += str(i)
                        else:
                            tmp_str += ','+str(i)
                        j += 1

                    tmp_str += '};'
                    event_msg_handlers.append(tmp_str);
                    event_msg_handlers.append('void* values[%d] = {};' % len(idList))

                    tmp_str = ""
                    j = 0
                    local_name = 'tmp_j'
                    #print(eventParaList)
                    while j < len(idList):
                        stri = ''
                        strs = ''

                        if idList[j] in eventParaList:
                            #print(monitorParams)
                            #print(idList[j])
                            stri =  'var%d;' % (eventParaList_[idList[j]] + 1)
                            #print(stri)
                            strs =  '(void*) var%d;' % (eventParaList_[idList[j]] + 1)
                        else:
                            stri = '(atoi(monitor_parameter_val_strs[identity[' + str(j)+']]));'
                            strs = '(void*)monitor_parameter_val_strs[identity[' + str(j)+']];\n'
                        tmp_str += 'if (target_parameterTypes[identity[' + str(j)+']]==INT) {int '+ local_name + ' = ' + stri
                        tmp_str += 'values[' + str(j) + '] =(void*)&' + local_name +';}'
                        tmp_str += 'else if(target_parameterTypes[identity[' + str(j)+']]==STRING) {values[' + str(j)+']=' + strs + '}\n'
                        tmp_str += 'else {values[' + str(j)+'] = (void *)NULL;}\n'
                        j += 1
                    event_msg_handlers.append(tmp_str);

                # Create a parameter list
                event_msg_handlers.append('param *p_head = NULL;')
                idx = 1
                for c_type in ev_params_c:
                    if c_type == 'int':
                        event_msg_handlers.append('push_param(&p_head, &var%d, NULL, NULL, NULL, NULL);' % (idx))
                    elif c_type == 'char':
                        event_msg_handlers.append('push_param(&p_head, NULL, &var%d, NULL, NULL, NULL);' % (idx))
                    elif c_type == 'double':
                        event_msg_handlers.append('push_param(&p_head, NULL, NULL, &var%d, NULL, NULL);' % (idx))
                    else:
                        event_msg_handlers.append('push_param(&p_head, NULL, NULL, NULL, &var%d, NULL);' % (idx))
                    idx += 1
                event_msg_handlers.append('push_param(&p_head, NULL, NULL, NULL, NULL, pro);')

                # Call handler
                event_msg_handlers.append('printf("%s calling import API for %s\\n");' % (sync_set_name, conn.targetMachine))
                event_msg_handlers.append('import_event_%s(identity, %s, values, %d, %s_%s_EVENT, p_head);' % (conn.targetMachine.lower(), type, len(idList), conn.targetMachine.upper(), conn.targetEvent.upper()))
                event_msg_handlers.append('}' * len(ev_params_c))
                
                if len(ev_params) > 0:
                    event_msg_handlers.append('} else {')
                    event_msg_handlers.append('printf("no parameters\\n");\n}')
                event_msg_handlers.append('} else ')
        # We could print a message when an event comes in with a routing key we don't recognize, but let's just silently ignore it for efficiency.
        event_msg_handlers.append(';');

        values['event_msg_handlers'] = '\n'.join(event_msg_handlers)

        # Global wrapper sync_queue handling
        sync_queue_handlers = dict() # key is monitor name
                                     # value is another dict with event/callstring pairs
        for mon in sync_set_monitors:
            sync_queue_handlers[mon] = dict()
        for conn in mg.archSpec:
            if conn.targetMachine in sync_set_monitors and conn.sourceMachine in sync_set_monitors:
                callstring = ['{']
                callstring.append('int dest_event_id = %s_%s_EVENT;' % (conn.targetMachine.upper(), conn.targetEvent.upper()))

                connSpec = conn.patternSpec
                idType = ''
                identityList = []
                if connSpec == None or len(connSpec) == 0:
                    idType = "INT" # It really doesn't matter as long as it's a valid SMEDL type
                    callstring.append('int *identity = NULL;')
                    callstring.append('void **values = NULL;')
                else:
                    # * create identity array with indices of identities to match
                    # from the pattern spec
                    # * create values array from event params or exporting monitor identity
                    # * create type var from the type of the first identity used
                    identityLines = []
                    i = 0
                    for pattern in connSpec:
                        if pattern.leftTerm != conn.targetMachine:
                            exit("Illegal pattern: Left term(%s) must be the target machine" % pattern.leftTerm)
                        if pattern.rightTerm == conn.sourceEvent:
                            # This identity comes from the event parameters.
                            identityLines.append("p = params;")
                            identityLines.append("for (int i = 0; i < %d; i++) {" % pattern.rightIndex)
                            identityLines.append("p = p->next;")
                            identityLines.append("}")
                            if mg._getMachine(conn.targetMachine).params[pattern.leftIndex] == "int":
                                identityLines.append("values[%d] = &(p->i);" % i)
                            else: # It's a string or some other type that uses the a pointer (v)
                                identityLines.append("values[%d] = p->v;" % i)
                        elif pattern.rightTerm == conn.sourceMachine:
                            # This identity comes from the source machine's identities
                            identityLines.append("values[%d] = identities[%d]->value;" % (i, pattern.rightIndex))
                        else:
                            exit("Illegal pattern: Right term (%s) must be either source machine or source event" % pattern.rightTerm)
                        identityList.append(pattern.leftIndex)
                        i += 1

                    idType = mg._getMachine(conn.targetMachine).params[0].upper()
                    identityList_str = "int identity[%d] = {" % len(identityList)
                    first_id = True
                    for ident in identityList:
                        if first_id:
                            first_id = False
                        else:
                            identityList_str += ", "
                        identityList_str += str(ident)
                    identityList_str += "};"
                    callstring.append(identityList_str)
                    callstring.append("void *values[%d] = {};" % len(identityList))
                    callstring.append("param *p;")
                    callstring.extend(identityLines)

                callstring.append('#ifdef DEBUG')
                callstring.append('printf("\\n%s set calling import API for %s.%s (from %s.%s)");' %
                        (sync_set_name, conn.targetMachine, conn.targetEvent,
                            conn.sourceMachine, conn.sourceEvent))
                callstring.append('#endif //DEBUG')
                callstring.append('import_event_%s(identity, %s, values, %d, dest_event_id, params);' %
                        (conn.targetMachine.lower(), idType, len(identityList)))
                callstring.append('}')

                if conn.sourceMachine not in sync_queue_handlers or conn.sourceEvent not in sync_queue_handlers[conn.sourceMachine]:
                    sync_queue_handlers[conn.sourceMachine][conn.sourceEvent] = callstring
                else:
                    sync_queue_handlers[conn.sourceMachine][conn.sourceEvent].extend(callstring)
        values['sync_queue_handlers'] = []
        for k, v in sync_queue_handlers.items():
            event_list = list()
            for ev, callstring in v.items():
                event_list.append({'event_name':ev, 'callstring': '\n'.join(callstring)})
            values['sync_queue_handlers'].append({'monitor_name':k, 'event_list':event_list})

        # End of wrappers ###################################################

        parameterTypeNumMap = collections.OrderedDict()
        parameterTypeNumMap['int'] = 0
        parameterTypeNumMap['float'] = 0
        parameterTypeNumMap['double'] = 0
        parameterTypeNumMap['pointer'] = 0
        parameterTypeNumMap['thread'] = 0
        parameterTypeNumMap['string'] = 0
        parameterTypeNumMap['opaque'] = 0
        parameterTypeNumMap['char'] = 0

        for m in methods:
            #print (m)
            eventFunction = []
            probeFunction = []
            params = ''
            identityParams = []
            callstring = ''
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

            monitorParams=[]
            # if m is an exported event and there is no transition triggered by it, we need to generate a signature with new names
            
            tpar = mg._symbolTable.get(m, 'params')
            if (tpar == None or not isinstance (tpar,list)) :
                continue
            if len(tpar) >0 and not isinstance (tpar[0],dict):
                continue

                    
            if CTemplater._checkParametersLiteral(mg,m):
                #print ('title:'+obj.title())
                monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}]
                index = 0
                for p in mg._symbolTable.get(m, 'params'):
                    monitorParams += [{'name':'v'+str(index),'c_type': CTemplater.convertTypeForC(p['type'])}]
                    index = index + 1
                monitorParams += [{'name':'provenance','c_type': 'cJSON *'}]
            else:
                #print('title:'+obj)
                #print ('title:'+obj.title())
                monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                    [{'name': p['name'], 'c_type': CTemplater.convertTypeForC(p['type'])} for p in mg._symbolTable.get(m, 'params')]
                monitorParams += [{'name':'provenance','c_type': 'cJSON *'}]

            tmp_map = {
                'int': 0,
                'float': 0,
                'double': 0,
                'pointer': 0,
                'thread': 0,
                'string':0,
                'opaque': 0,
                'char': 0
            }

            i = 0
            d = 0
            v = 0
            c = 0
            attrstring = ''
            for p in mg._symbolTable.get(m,'params'):
                tmp_map[p['type']] = tmp_map[p['type']]+1
                if p['type'] == 'int':
                    attrstring += ', i'+str(i)
                    i += 1
                elif p['type'] == 'char':
                    attrstring += ', c'+str(i)
                    c += 1
                elif p['type'] == 'double' or p['type'] == 'float':
                    attrstring += ', d'+str(d)
                    d += 1
                elif p['type'] == 'pointer' or key == 'opaque':
                    attrstring += ', v'+str(v)
                    v += 1
                elif p['type'] == 'string':
                    attrstring += ', v'+str(v)
                    v += 1
            attrstring += ', pro'
            parastring = ''
            ki = 0
            kd = 0
            kv = 0
            kc = 0
            for p in mg._symbolTable.get(m,'params'):
                if p['type'] == 'int':
                    parastring += '\t\ti' + str(ki) + ' = ((params)->i);\n'
                    ki += 1
                elif p['type'] == 'char':
                    parastring += '\t\tc' + str(kc) + ' = ((params)->c);\n'
                    kc += 1
                elif p['type'] == 'double' or p['type'] == 'float':
                    parastring += '\t\td' + str(kd) + ' = ((params)->d);\n'
                    kd += 1
                elif p['type'] == 'pointer' or key == 'opaque':
                    parastring += '\t\tv' + str(kv) + ' = ((params)->v);\n'
                    kv += 1
                elif p['type'] == 'string':
                    parastring += '\t\tv' + str(kv) + ' = ((params)->v);\n'
                    kv += 1
                parastring += '\t\t(params) = (params)->next;\n'
            parastring += 'pro = ((params)->provenance);\n\t\t(params) = (params)->next;\n'
            parastring += '\t\tpop_param(&p_head);\n'

            callstring += parastring;
            callstring += '\t\tpop_action(head);\n'
            callstring_ex = callstring
            callstring += '\t\t' + obj.lower() + '_' + m + '(monitor'+attrstring+');\n'
            callstring_ex += '\t\texported_' + obj.lower() + '_' + m + '(monitor'+attrstring+');\n'

            for key, value in parameterTypeNumMap.items():
                if tmp_map[key] > value:
                    parameterTypeNumMap[key] = tmp_map[key]
            eventSignature = 'void %s_%s(%s)' % (obj.lower(), m, ", ".join(['%s %s'%(p['c_type'], p['name']) for p in monitorParams]))
            #print (eventSignature)
            values['signatures'].append(eventSignature)
            eventFunction.append(eventSignature + ' {')
            for key, fsm in allFSMs.items():
                trans_group = fsm.groupTransitionsByStartState(fsm.getTransitionsByEvent(str(m)))
                final_states = fsm.finalstates
                # Jump to next FSM if this one contains no transitions for the current event
                if len(trans_group) == 0:
                    continue

                reference = 'monitor->state[%s_%s_SCENARIO]' % (obj.upper(), key.upper())
                name_reference = "%s_states_names[%s_%s_SCENARIO][monitor->state[%s_%s_SCENARIO]]"%(obj.lower(), obj.upper(), key.upper(), obj.upper(), key.upper())
                eventFunction.append('if (%s_executed_scenarios[%s_%s_SCENARIO]==0) {' % (obj.lower(), obj.upper(), key.upper()))
                eventFunction.append('  switch (%s) {' % reference)
                for start_state, transitions in trans_group.items():
                    #print(transitions[0])
                    eventFunction.append(CTemplater._writeCaseTransition(mg, obj, transitions, reference, name_reference, key, final_states))
                if mg._implicitErrors:
                    eventFunction.append('    default:')
                    eventFunction.append('      raise_error(\"%s_%s\", %s, \"%s\", \"DEFAULT\");' % (obj.lower(), key, name_reference, m))
                    
                    #  eventFunction.append('      goto exec;') #add at 09/20
                    eventFunction.append('      break;')
                eventFunction.append('  }')
                eventFunction.append('//%s_executed_scenarios[%s_%s_SCENARIO]=1;' % (obj.lower(), obj.upper(), key.upper()))
                eventFunction.append('  }')
    #eventFunction.append('exec:') #add at 09/20
            eventFunction.append('executeEvents_%s(monitor);' % (obj.lower()))
            eventFunction.append('}\n\n')

            export_event_sig = None
            cjson_str = '\tcJSON *root; cJSON* fmt; cJSON* prove; \n\t root = cJSON_CreateObject();\n'
            if 'exported_events' == mg._symbolTable.get(m)['type']:
                #paramString = obj.title() + "Monitor* monitor " + CTemplater._generateEventParams(mg,m)
                paramString = "MonitorIdentity** identities" + CTemplater._generateEventParams(mg,m)
                export_event_sig = 'void exported_%s_%s(%s)' % (obj.lower(), m, paramString)
                values['signatures'].append(export_event_sig)
                eventFunction.append(export_event_sig + ' {')
                eventFunction.append('  char* message;')
                evParams = mg._getEventParams(paramString)[1:]
                cjson_str+=('\tcJSON_AddItemToObject(root, "name", cJSON_CreateString("%s_%s"));\n') % (obj.lower(), m)
                cjson_str+=('\tcJSON_AddItemToObject(root, "fmt_version", cJSON_CreateString(msg_format_version));\n')
                cjson_str+=('\tcJSON_AddItemToObject(root, "params", fmt = cJSON_CreateObject());\n')
                sprintf = ''
                index = 1
                if len(evParams) > 0:
                    for p in evParams:
                        # comparing SMEDL types not C types.
                        if p[0] == 'int':
                            sprintf += 'cJSON_AddNumberToObject(fmt, "v%d",%s);\n' % (index,p[1])
                        elif p[0] == 'char':
                            sprintf += 'cJSON_AddNumberToObject(fmt, "v%d",%s);\n' % (index,p[1])
                        elif p[0] == 'double':
                            sprintf += 'cJSON_AddNumberToObject(fmt, "v%d",%s);\n' % (index,p[1])
                        elif p[0] == 'float':
                                exit("this should never happen. there is a missing float->double conversion.")
                        elif p[0] == 'char*':
                            sprintf += 'cJSON_AddStringToObject(fmt, "v%d",%s);\n' % (index,p[1])
                        index = index + 1
                cjson_str+=("if (provenance!=NULL){\n cJSON_AddItemToObject(root, \"provenance\", prove = provenance);}\n\t")
                sprintf += 'message = cJSON_Print(root);\n'
                eventFunction.append(cjson_str)
                eventFunction.append(sprintf)
                eventFunction.append('  char routing_key[256];')

                # Construct routing key
                name = mg._symbolTable.getSymbolsByType('object')[0]
                connName = None
                for conn in mg.archSpec:
                    if conn.sourceMachine == name and conn.sourceEvent == m:
                        connName = conn.connName
                        break
                if connName == None:
                    connName = obj+'_'+ m
                sprintf_routing = '  sprintf(routing_key, "%s' % (connName)
                # TODO: peter, write functions for printing and parsing monitor identities
                # this cast is broken and wrong, but works as long as we have only one monitor process

                for v in identities:
                    #print("mg:"+v)
                    
                    if v['type'] == 'string':
                        sprintf_routing += '.%s'
                    else:
                        sprintf_routing += '.%ld'
                sprintf_routing += '.'+m
                if len(evParams) > 0:
                    for p in evParams:
                        #print(p[0])
                        # attributes can only be int
                        if p[0] == 'int':
                            sprintf_routing += '.%d'
                        elif p[0] == 'string':
                            sprintf_routing += '.%s'
                        elif p[0] != 'cJSON*' :
                            sprintf_routing += '.0'

                sprintf_routing+='"'
                for v in identities:
                    if v['type'] == 'string':
                        sprintf_routing += ', (char*)((identities['
                    else:
                        sprintf_routing += ', (long)(*(int*)(identities['
                    sprintf_routing += '%s_' % obj.upper() # TODO: Update this value with exact identity name defined in SMEDL
                    sprintf_routing += v['name'].upper() +']->value))'
                if len(evParams) > 0:
                    for p in evParams:
                # attributes can only be int
                        if p[0] == 'int':
                            sprintf_routing+=', %s' % p[1]
                sprintf_routing += ');'
                eventFunction.append(sprintf_routing)
                #add to test
                eventFunction.append('printf("msg:%s\\n", message);');
                eventFunction.append('  send_message(message, routing_key);')
                eventFunction.append('}\n\n')
            raiseFunction = CTemplater._writeRaiseFunction(mg, m, obj, sync_set_name)

            # Build the event handler function
            if pedlEvent:
                probeParams = [p for p in monitorParams if p['name'] != 'monitor']
                probeSignature = 'void %s_%s_probe(%s%s%s)' % (obj.lower(), m, ", ".join(['%s %s'%(p['c_type'], p['name']) for p in identityParams]), ", ".join(['%s %s'%(p['c_type'], p['name']) for p in probeParams]),",cJSON * provenance")
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
                if 'imported_events' != mg._symbolTable.get(m)['type']:
                    values['pending_event_case'].append({'event_enum':[obj.upper()+'_'+m.upper()+'_EVENT:'],'callstring':callstring})
                if 'exported_events' == mg._symbolTable.get(m)['type']:
                    values['export_event_case'].append({'event_enum':[obj.upper()+'_'+m.upper()+'_EVENT:'],'callstring':callstring_ex})
            else:
                values['event_code'].append(CTemplater._updateVarNames(mg, {'event':eventFunction, 'raise':raiseFunction['code']}, m))
                if 'imported_events' != mg._symbolTable.get(m)['type']:
                    values['pending_event_case'].append({'event_enum':[obj.upper()+'_'+m.upper()+'_EVENT:'],'callstring':callstring})
                if 'exported_events' == mg._symbolTable.get(m)['type']:
                    values['export_event_case'].append({'event_enum':[obj.upper()+'_'+m.upper()+'_EVENT:'],'callstring':callstring_ex})
            values['signatures'].append(raiseFunction['signature'])
            callCases.append(CTemplater._writeCallCase(mg, m))

        # Construct var_declaration
        t_str = ''
        floatNum = parameterTypeNumMap['float']
        for key,value in parameterTypeNumMap.items():
            if value > 0:
                t_str += CTemplater.convertTypeForC(key) + ' '
            #print (t_str)
            iterBegin = 0
            iterEnd = value
            if key == 'double':
                iterBegin = floatNum
                iterEnd = floatNum + value
            for k in range(iterBegin,iterEnd):
                if k != iterEnd-1:
                    if key == 'string':
                        t_str += 'v' + str(k) + ', '
                
                    else:
                        t_str += CTemplater.convertTypeForC(key)[0] + str(k) + ', '
                else:
                    if key == 'string':
                        t_str += 'v' + str(k) + '; '
                    else:
                        t_str += CTemplater.convertTypeForC(key)[0] + str(k) + '; '
        values['var_declaration'] = t_str

        # Render the monitor templates and write to disk
        env = Environment(loader=PackageLoader('smedl.c_style','.'))
        basename = os.path.basename(filename)
        dirname = os.path.dirname(filename)
        if output_dir is None:
            output_dir = ''
        os.makedirs(os.path.join(dirname, output_dir), exist_ok=True)

        out_h = env.get_template('object_mon.h').render(values)
        if console_output:
            print("--" + filename + "_mon.h--")
            print(out_h)
        else:
            out_h_file = open(os.path.join(dirname, output_dir, basename + '_mon.h'), 'w')
            out_h_file.write(out_h)
            out_h_file.close()

        out_c = env.get_template('object_mon.c').render(values)
        if console_output:
            print("--" + filename + "_mon.c--")
            print(out_c)
        else:
            out_c_file = open(os.path.join(dirname, output_dir, basename + '_mon.c'), 'w')
            out_c_file.write(out_c)
            out_c_file.close()

        out_wh = env.get_template('monitor_wrapper.h').render(values)
        if console_output:
            print("--" + filename + "_monitor_wrapper.h--")
            print(out_wh)
        else:
            out_wh_file = open(os.path.join(dirname, output_dir, basename + '_monitor_wrapper.h'), 'w')
            out_wh_file.write(out_wh)
            out_wh_file.close()
        
        out_w = env.get_template('monitor_wrapper.c').render(values)
        if console_output:
            print("--" + filename + "_monitor_wrapper.c--")
            print(out_w)
        else:
            out_w_file = open(os.path.join(dirname, output_dir, basename + '_monitor_wrapper.c'), 'w')
            out_w_file.write(out_w)
            out_w_file.close()
        
        glb_h = env.get_template('set_global_wrapper.h').render(values)
        if console_output:
            print("--" + os.path.join(dirname, sync_set_name + "_global_wrapper.h--"))
            print(glb_h)
        else:
            glb_h_file = open(os.path.join(dirname, output_dir, sync_set_name + '_global_wrapper.h'), 'w')
            glb_h_file.write(glb_h)
            glb_h_file.close()
        
        glb_c = env.get_template('set_global_wrapper.c').render(values)
        if console_output:
            print("--" + os.path.join(dirname, sync_set_name + "_global_wrapper.c--"))
            print(glb_c)
        else:
            glb_c_file = open(os.path.join(dirname, output_dir, sync_set_name + '_global_wrapper.c'), 'w')
            glb_c_file.write(glb_c)
            glb_c_file.close()

        # Copy pre-written static helper files to the output path
        a_h = env.get_template('actions.h').render()
        if console_output:
            print("--actions.h--")
            print(a_h)
        else:
            a_h_file = open(os.path.join(dirname, output_dir, 'actions.h'), 'w')
            a_h_file.write(a_h)
            a_h_file.close()

        a_c = env.get_template('actions.c').render()
        if console_output:
            print("--actions.c--")
            print(a_c)
        else:
            a_c_file = open(os.path.join(dirname, output_dir, 'actions.c'), 'w')
            a_c_file.write(a_c)
            a_c_file.close()

        cjson_h = env.get_template('cJSON.h').render()
        if console_output:
            print("--cJSON.h--")
            print(cjson_h)
        else:
            cjson_h_file = open(os.path.join(dirname, output_dir, 'cJSON.h'), 'w')
            cjson_h_file.write(cjson_h)
            cjson_h_file.close()

        cjson_c = env.get_template('cJSON.c').render()
        if console_output:
            print("--cJSON.c--")
            print(cjson_c)
        else:
            cjson_c_file = open(os.path.join(dirname, output_dir, 'cJSON.c'), 'w')
            cjson_c_file.write(cjson_c)
            cjson_c_file.close()

        m_h = env.get_template('monitor_map.h').render()
        if console_output:
            print("--monitor_map.h--")
            print(m_h)
        else:
            m_h_file = open(os.path.join(dirname, output_dir, 'monitor_map.h'), 'w')
            m_h_file.write(m_h)
            m_h_file.close()

        m_c = env.get_template('monitor_map.c').render()
        if console_output:
            print("--monitor_map.c--")
            print(m_c)
        else:
            m_c_file = open(os.path.join(dirname, output_dir, 'monitor_map.c'), 'w')
            m_c_file.write(m_c)
            m_c_file.close()

        u_h = env.get_template('amqp_utils.h').render()
        if console_output:
            print("--amqp_utils.h--")
            print(u_h)
        else:
            u_h_file = open(os.path.join(dirname, output_dir, 'amqp_utils.h'), 'w')
            u_h_file.write(u_h)
            u_h_file.close()

        u_c = env.get_template('amqp_utils.c').render()
        if console_output:
            print("--amqp_utils.c--")
            print(u_c)
        else:
            u_c_file = open(os.path.join(dirname, output_dir, 'amqp_utils.c'), 'w')
            u_c_file.write(u_c)
            u_c_file.close()

        mu_h = env.get_template('mon_utils.h').render()
        if console_output:
            print("--mon_utils.h--")
            print(mu_h)
        else:
            mu_h_file = open(os.path.join(dirname, output_dir, 'mon_utils.h'), 'w')
            mu_h_file.write(mu_h)
            mu_h_file.close()

        mu_c = env.get_template('mon_utils.c').render()
        if console_output:
            print("--mon_utils.c--")
            print(mu_c)
        else:
            mu_c_file = open(os.path.join(dirname, output_dir, 'mon_utils.c'), 'w')
            mu_c_file.write(mu_c)
            mu_c_file.close()


    def _checkParametersLiteral(mg,m):
        #print (mg._symbolTable)

        for p in mg._symbolTable.get(m, 'params'):
                #print(p['name'])
            if len(p['name'])>0:
                if p['name'][0]=='\"' or p['name'][0]== '-' or p['name'][0]=='+' or p['name'][0].isdigit():
                    return True
        return False

    # Major changes for synchronous communication:
    # Takes all channels that come into any monitor in the synchronous set from outside it
    # Return only the channel names
    def _getBindingKeys(mg, sync_set_monitors):
        lst = []
        for conn in mg.archSpec:
            if conn.targetMachine in sync_set_monitors and conn.sourceMachine not in sync_set_monitors:
                lst.append(conn.connName)
        return lst

    #for dynamic instantiation, no need to analyze routing key when building binding keys
    def _getBindingKeys2(mg):
        lst = []
        name = mg._symbolTable.getSymbolsByType('object')[0]
        k = 0
        for conn in mg.archSpec:
            #print (str(k))
            if name==conn.targetMachine:
                b_str = 'bindingkeys['+str(k)+']'
                p_str = b_str + '=(char*)malloc(255*sizeof(char));\n'+'\tstrcpy('+b_str+',"'+conn.connName+'");\n'
                sourceMachine = mg._getMachine(conn.sourceMachine)
                #print(sourceMachine)
                #if sourceMachine == None:
                #    raise ValueError('source machine not exist')
                sourceEvent = mg._getSourceEvent(conn.sourceMachine,conn.sourceEvent)
                #if sourceEvent == None:
                #raise ValueError('source event not exist')
                lst.append(p_str+'strcat('+b_str+',".#");\n')
                k = k + 1

        bindingkey = ''
        i = 0
        for s in lst:
            bindingkey += s
            i = i+1
        if len(lst)==0:
            bindingkey+='bindingkeys[0]=(char*)malloc(255*sizeof(char));\n'+'\tstrcpy(bindingkeys[0],"#");\n'
                #print (bindingkey)
        return bindingkey

    def _getBindingKeys1(mg):
        lst = []
        name = mg._symbolTable.getSymbolsByType('object')[0]
        k = 0
        for conn in mg.archSpec:
            b_str = 'bindingkeys['+str(k)+']'
            if name==conn.targetMachine:
                p_str = b_str + '=(char*)malloc(255*sizeof(char));\n'+'\tstrcpy('+b_str+',"'+conn.connName+'");\n'
                sourceMachine = mg._getMachine(conn.sourceMachine)
                #print(sourceMachine)
                #if sourceMachine == None:
                #    raise ValueError('source machine not exist')
                sourceEvent = mg._getSourceEvent(conn.sourceMachine,conn.sourceEvent)
                    #if sourceEvent == None:
                    #raise ValueError('source event not exist')
                if conn.patternSpec == [] or conn.patternSpec == None:
                    lst.append(p_str+'strcat('+b_str+',".#");\n')
                else:
                    machineIndexDic = {}
                    eventIndexDic = {}
                    #TODO: generate predicates on the machine and event, add corresponding filter, for each target event, union all predicates
                    for p_spec in conn.patternSpec:

                        leftterm = p_spec.getLeftTerm()
                        rightterm = p_spec.getRightTerm()
                        if leftterm == rightterm or (not leftterm == conn.targetMachine and not rightterm == conn.targetMachine) or (leftterm == conn.targetEvent and not conn.sourceEvent == conn.targetEvent ) or (rightterm == conn.targetEvent and not conn.sourceEvent == conn.targetEvent ):

                            raise ValueError('pattern expression syntax error')
                        else:
                            leftindex = p_spec.getLeftIndex()
                            rightindex = p_spec.getRightIndex()
                            if mg._checkBound(conn,leftterm,leftindex) and mg._checkBound(conn,rightterm,rightindex):
                                if leftterm == conn.targetMachine:
                                    val = mg._getIdentityName(leftindex)
                                    if not val == None:
                                        if rightterm == conn.sourceEvent:
                                            eventIndexDic[rightindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                                        elif rightterm == conn.sourceMachine:
                                            machineIndexDic[rightindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                                elif rightterm == conn.targetMachine:
                                    val = mg._getIdentityName(rightindex)
                                    if not val == None:
                                        if leftterm == conn.sourceEvent:
                                            eventIndexDic[leftindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                                        elif leftterm == conn.sourceMachine:
                                            machineIndexDic[leftindex] = 'monitor->identities['+name.upper()+'_'+val.upper()+']'
                            else:
                                raise ValueError('out of bound in pattern expression')
                    #build binding key and add it to lst
                    machineIndex = 0
                    eventIndex = 0
                    while sourceMachine != None and machineIndex < len(sourceMachine.params):
                        if not machineIndex in machineIndexDic.keys():
                            p_str += '\tstrcat('+b_str+',".*");\n'
                        else:
                            p_str += '\tstrcat('+b_str+',".");\n'
                            p_str += '\tstrcat('+b_str+',monitor_identity_str('+machineIndexDic[machineIndex]+'));\n'
                        machineIndex = machineIndex + 1

                    p_str +='\tstrcat('+b_str+',".'+sourceEvent.event_id+'");\n'
                    while eventIndex < len(sourceEvent.params):
                        if not eventIndex in eventIndexDic.keys():
                            p_str += '\tstrcat('+b_str+',".*");\n'
                        else:
                            p_str += '\tstrcat('+b_str+',".");\n'
                            p_str += '\tstrcat('+b_str+',monitor_identity_str('+eventIndexDic[eventIndex]+'));\n'
                        eventIndex = eventIndex + 1
                    lst.append(p_str)
                k = k + 1
        bindingkey = ''
        i = 0
        for s in lst:
            bindingkey += s
            i = i+1
        if len(lst)==0:
            bindingkey+='bindingkeys[0]=(char*)malloc(255*sizeof(char));\n'+'\tstrcpy(bindingkeys[0],"#");\n'
        return bindingkey


    # Translate a SMEDL type to a C type
    @staticmethod
    def convertTypeForC(smedlType):
        typeMap =  {
            'int': 'int',
            'float': 'double',
            'double': 'double',
            'pointer': 'void*',
            'thread': 'pthread_t',
            'opaque': 'void*',
            'string': 'char*',
            'char': 'char'
        }
        if smedlType in typeMap:
            return typeMap[smedlType]
        else:
            return smedlType


    @staticmethod
    def _updateVarNames(mg, funcs, method):
        out = {}
        for name, func in funcs.items():
            tmp = func
            for p in mg._symbolTable.get(method, 'params'):
                #print(p)
                out_s = []
                for s in tmp:
                    out_s.append(re.sub(r'\b' + p['true_name'] + r'\b', p['name'], s))
                tmp = out_s
            out[name] = tmp
        return out


    # Write out the switch statement case for a SMEDL trace transition
    @staticmethod
    def _writeCaseTransition(mg, obj, transitions, currentState, stateName, scenario, finalstates):
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
            
            #print(transitions[i].guard)
            if i == 0 and transitions[i].guard:
                output.append('      if(' + transitions[i].guard.replace('this.', 'monitor->') + ') {\n')
                
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                if transitions[i].nextState.name in finalstates:
                    output.append('monitor->recycleFlag = 1;\n')
                output.append('      }\n')
            elif len(transitions) == 1:
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('      %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                if transitions[i].nextState.name in finalstates:
                    output.append('monitor->recycleFlag = 1;\n')
                break
            elif transitions[i].guard:
                output.append('      else if(' + transitions[i].guard.replace('this.', 'monitor->') + ') {\n')
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                if transitions[i].nextState.name in finalstates:
                    output.append('monitor->recycleFlag = 1;\n')
                output.append('      }\n')

            # Handle Else (an Else state is defined, or reaching an Else denotes an error condition)
            if transitions[i].elseState and ((i+1 < len(transitions) and transitions[i+1].guard is None) or i+1 == len(transitions)):
                output.append('      else {\n')
                if transitions[i].elseActions:
                    for action in transitions[i].elseActions:
                        output.append('        %s\n' % mg._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].elseState.name)).upper() + ';\n')
                if transitions[i].elseState.name in finalstates:
                    output.append('monitor->recycleFlag = 1;\n')
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
            params = mg._getEventParams(paramString)
            for p in params:
                output.append('      %s %s_%s = monitor->action_queue->params->%c;' % (p[0], p[1], event, p[0][0]))
                output.append('      pop_param(&monitor->action_queue->params);')
            callParams = ", ".join('%s_%s' % (p[1], event) for p in params)
            output.append('      %s(%s);' % (event, ", ".join(['monitor', callParams])))
        output.append('      break;')
        return '\n'.join(output)


    def _generateEventParams(mg,event):
        paramString = ''
        index = 0
        for p in mg._symbolTable.get(event, 'params'):
            paramString+=', '+ CTemplater.convertTypeForC(p['type'])+' v'+str(index)
            index += 1
        paramString+=', cJSON* provenance'
        return paramString


    def _writeRaiseFunction(mg, event, obj, sync_set_name):
        output = []
        paramString = obj.title() + "Monitor* monitor" + CTemplater._generateEventParams(mg,event)
        signature = 'void raise_%s_%s(%s)' % (obj.lower(), event, paramString)
        output.append(signature + ' {')
        output.append('  param *p_head = NULL;')
        # Another param for exported event
        if 'exported_events' == mg._symbolTable.get(event)['type']:
            output.append(' param *ep_head = NULL;')
        if len(paramString) > 0:
            for p in mg._getEventParams(paramString):
                # Comparing SMEDL types not C types.
                if p[0] == 'int':
                    output.append('  push_param(&p_head, &%s, NULL, NULL, NULL,NULL);' % p[1])
                    if 'exported_events' == mg._symbolTable.get(event)['type']:
                        output.append('  push_param(&ep_head, &%s, NULL, NULL, NULL,NULL);' % p[1])
                elif p[0] == 'char':
                    output.append('  push_param(&p_head, NULL, &%s, NULL, NULL,NULL);' % p[1])
                    if 'exported_events' == mg._symbolTable.get(event)['type']:
                        output.append('  push_param(&ep_head, NULL, &%s, NULL, NULL,NULL);' % p[1])
                elif p[0] == 'float':
                    exit("this should never happen. there is a missing float->double conversion.")
                elif p[0] == 'double':
                    output.append('  push_param(&p_head, NULL, NULL, &%s, NULL,NULL);' % p[1])
                    if 'exported_events' == mg._symbolTable.get(event)['type']:
                        output.append('  push_param(&ep_head, NULL, NULL, &%s, NULL,NULL);' % p[1])
                elif p[0] == 'pointer' or p[0] == 'char*':
                    output.append('  push_param(&p_head, NULL, NULL, NULL, &%s,NULL);' % p[1])
                    if 'exported_events' == mg._symbolTable.get(event)['type']:
                        output.append('  push_param(&ep_head, NULL, NULL, NULL, &%s,NULL);' % p[1])
        output.append(' push_param(&p_head, NULL, NULL, NULL, NULL,provenance);')
        if 'exported_events' == mg._symbolTable.get(event)['type']:
            output.append(' push_param(&ep_head, NULL, NULL, NULL, NULL,provenance);')
        output.append('  push_action(&monitor->action_queue, %s_%s_EVENT, p_head);' % (obj.upper(), event.upper()))
        if 'exported_events' == mg._symbolTable.get(event)['type']:
            #output.append('  push_action(&monitor->export_queue, %s_%s_EVENT, ep_head);' % (obj.upper(), event.upper()))
            output.append('  export_event(%s_%s_MONITOR, monitor->identities, %s_%s_EVENT, ep_head);' % (sync_set_name.upper(), obj.upper(), obj.upper(), event.upper()))
        output.append('}\n\n')
        return {'code':output, 'signature':signature}
