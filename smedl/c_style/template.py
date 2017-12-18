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
                if s['type'] == 'int' or s['type'] == 'float':
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
            print (s)
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
        values['mon_init_str'] = []
        # If there are no identities defined, make a default one:
        if len(mg._symbolTable.getSymbolsByType('identity')) == 0:
            identities = [{'type': 'opaque', 'name': 'id'}]
            #if there are no identities defined, add creation of default monitor instances
            mon_init_handler = []
            implicit_data_name = 'implicit_d'#implicit temp data name
            mon_init_handler.append('%sData *%s = (%sData *)malloc(sizeof(%sData));\n' %(obj.title(),implicit_data_name,obj.title(),obj.title()))
            #TODO: need add statement adding initial value of state variables
            implicit_str = 'int i = 0;\n'
            implicit_str += implicit_data_name + '-> id = &i;\n'
            implicit_str += CTemplater._addDataString(implicit_data_name, state_vars)

            #for s in state_vars:
            #    v = 'NULL'
            #    if s['type'] == 'int' or s['type'] == 'float':
            #        v = '0'
            #    elif s['type'] == 'string' :
            #        v = '\"0\"'
                #print(v)
                #    implicit_str += implicit_data_name + '->' + s['name'] + '=' + v + ';\n'
            mon_init_handler.append(implicit_str)
            mon_init_handler.append('%sMonitor *tempMon = init_%s_monitor(%s);\n' % (obj.title(),obj.lower(),implicit_data_name))
            mon_init_handler.append('tempMon -> send_conn = send_conn;\n')
            mon_init_handler.append('tempMon -> amqp_exchange = amqp_exchange;\n')
            values['mon_init_str'].append('\n'.join(mon_init_handler))
            
        else:
            identities = [{'type': mg._symbolTable.get(v)['datatype'], 'name': v} for v in mg._symbolTable.getSymbolsByType('identity')]
        for id in identities:
            id['c_type'] = CTemplater.convertTypeForC(id['type'])


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

        # Output a method for each event (switch statement to handle FSM transitions)
        methods = mg._symbolTable.getEvents()
        callCases = []
        values['signatures']= []
        values['event_code'] = []
        values['event_msg_handlers'] = []
        values['var_declaration'] = []
        values['pending_event_case'] = []
        values['export_event_case'] = []

        if mg._getBindingKeysNum() == 0:
            values['bindingkeys_num'] = 1 # TODO: Make these customizable
        else:
            values['bindingkeys_num'] = mg._getBindingKeysNum()# TODO: Make these customizable
        values['b_keys'] = CTemplater._getBindingKeys(mg)
        #print(values['b_keys'])


        # Construct event_msg_handlers
        name = mg._symbolTable.getSymbolsByType('object')[0]
        #print(name)
        for conn in mg.archSpec:
            if conn.targetMachine == name:
                monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                [{'name': p['name'], 'c_type': CTemplater.convertTypeForC(p['type']), 'type' : p['type']} for p in mg._symbolTable.get(conn.targetEvent, 'params')]
                msg_handler = []
                if len(values['event_msg_handlers']) == 0:
                    cond = 'if'
                else:
                    cond = '                else if'
                msg_handler.append(cond + ' (!strcmp(eventName,"%s")) {' % conn.connName)
                json_string = ''
                json_params_mark = 0
                if len(monitorParams[1:])>0:
                    json_params_mark = 1
                    json_string+= '\t cJSON * fmt = cJSON_GetObjectItem(root,"params");\n\t if (fmt!=NULL) {\n\t'
                retAttrs = ''
                retArray = []
                sscanfStr = ''
                index = 1
                print(monitorParams)
                for p in monitorParams[1:]:
                    if p['c_type'] == 'char*':
                        msg_handler.append('                    char *%s = NULL;' % (p['name']))
                    else:
                        msg_handler.append('                    %s %s = 0;' % (p['c_type'], p['name']))
                    
                    if p['c_type'] == 'int':
                        sscanfStr+=('if (cJSON_GetObjectItem(fmt,"v%d") != NULL) {\n\t\t' + p['name']+'= cJSON_GetObjectItem(fmt,"v%d")->valueint;\n\t') %(index,index)
                    elif p['c_type'] == 'char':
                        sscanfStr+=('if (cJSON_GetObjectItem(fmt,"v%d") != NULL) {\n\t\t' + p['name']+'= cJSON_GetObjectItem(fmt,"v%d")->valueint;\n\t') %(index,index)
                    elif p['c_type'] == 'float':
                        exit("this should never happen. there is a missing float->double conversion.")
                    elif p['c_type'] == 'double':
                        sscanfStr+=('if (cJSON_GetObjectItem(fmt,"v%d") != NULL) {\n\t\t' + p['name']+'= cJSON_GetObjectItem(fmt,"v%d")->valuedouble;\n\t') %(index,index)
                    elif p['c_type'] == 'char*':
                        sscanfStr+=('if (cJSON_GetObjectItem(fmt,"v%d")!= NULL) {\n\t\t' + p['name']+'= cJSON_GetObjectItem(fmt,"v%d")->valuestring;\n\t') %(index,index)
                    index = index + 1
                    retAttrs += ', ' + p['name']
                    retArray.append(p['name'])
            
                #get parameter list
                #print(conn.sourceMachine)
                #sscanfStr + = 'char* strs[' + '] = divideRoutingkey(rk,{{}});';
                lengthIdentityList = 0
                s_machine_params = []
                #if conn.sourceMachine != None and conn.sourceMachine != '' and conn.sourceMachine != ' ':
                #    s_machine = mg._getMachine(conn.sourceMachine)
                #    if s_machine != None:
                #        s_machine_params = s_machine.params
                #        lengthIdentityList = len(s_machine_params)
                #        sscanfStr += 'int parameterTypes [' + str(lengthIdentityList) + '] = {'
                #        i = 0
                #        for t in s_machine_params:
                #            if i == 0:
                #                sscanfStr += t.upper()
                #            else:
                #                sscanfStr += ',' + t.upper()
                #            i = i + 1
                #        sscanfStr += '};\n'
                if conn.sourceMachine != None and conn.sourceMachine != '' and conn.sourceMachine != ' ':
                    s_machine = mg._getMachine(conn.sourceMachine)
                    if s_machine != None:
                        s_machine_params = s_machine.params
                        lengthIdentityList = len(s_machine_params)
                        sscanfStr += 'int parameterTypes [' + str(lengthIdentityList) + '] = {'
                        i = 0
                        for t in s_machine_params:
                            if i == 0:
                                sscanfStr += t.upper()
                            else:
                                sscanfStr += ',' + t.upper()
                            i = i + 1
                        sscanfStr += '};\n'
                                #need to reimplement the mechanism of naming when generating c code to avoid naming conflicts
                #monitor_parameter_val_strs:
                if lengthIdentityList > 0:
                    #sscanfStr += 'char* monitor_parameter_val_strs[' + str(lengthIdentityList) + '] = divideRoutingkey(rk,'+str(lengthIdentityList)+');';
                    sscanfStr += 'char** monitor_parameter_val_strs = divideRoutingkey(rk,'+str(lengthIdentityList)+');';
                #sscanfStr + = 'void* values[' + lengthIdentityList + '] = {}'
                #sscanfStr + = 'for (int i = 0; i<' + lengthIdentityList + '; i++){\n'
                #sscanfStr + = 'if (parameterTypes[i]==INT) {value[i]=(void*)=& (atoi(monitor_parameter_val_strs[i]));}\n'
                #sscanfStr + = 'else if(parameterTypes[i]==STRING) {value[i]=(void*)monitor_parameter_val_strs[i];}\n'
                #sscanfStr + = 'else {value[i] = (void *)NULL;}\n'
                #sscanfStr + = '}\n'
                #'if (executed_scenarios[%s_%s_SCENARIO]==0) {' % (obj.upper(), key.upper())
                sscanfStr += '%sMonitorRecord* record;\n'  % obj.title()
                retAttrs += ', pro'
                #print (conn)
                connSpec = conn.patternSpec
                t_machine = mg._getMachine(conn.targetMachine)
                t_machine_params = t_machine.params
                t_lengthIdentityList = len(t_machine_params)
                sscanfStr += 'int target_parameterTypes [' + str (t_lengthIdentityList) + '] = {'
                i = 0
                for t in t_machine_params:
                    if i == 0:
                        sscanfStr += t.upper()
                    else:
                        sscanfStr += ',' + t.upper()
                    i = i + 1
                sscanfStr += '};\n'

                #print(t_machine)
                #print(conn.targetEvent)
                targetEvent = mg._getTargetEvent(conn.targetMachine,conn.targetEvent)
                
                #print (targetEvent)
                #print (targetEvent)
                
                if connSpec == None or len(connSpec) == 0:
                    # retrieve all instances
                    #print("empty")
                    sscanfStr +=  'record = get_%s_monitors();' % obj.lower()

                else:
                    #print (connSpec)
                    j = 0
                    idList = []
                    type = ""
                    #print (pattern)
                    eventParaList = []
                    for pattern in connSpec: #operator is always equal, leftTerm is identity of target monitor
                        if pattern.leftTerm != conn.targetMachine:
                            #print(pattern.leftTerm)
                            #print(conn)
                            exit("illegal pattern1")
                        #if s_machine_params == None or pattern.leftIndex >= len(s_machine_params) :
                        #    exit("illegal pattern2")
                        if pattern.rightTerm == conn.sourceEvent:
                            eventParaList.append(pattern.leftIndex)
                        if j == 0:
                            type = t_machine_params[pattern.leftIndex].upper()
                            j = 1
                        idList.append(pattern.leftIndex)
                
                    sscanfStr += 'int identity[' + str(len(connSpec)) +'] = {'
                    j = 0
                    for i in idList:
                        if j == 0:
                            sscanfStr += str(i)
                        else:
                            sscanfStr += ','+str(i)
                        j = j+1
                    
                    sscanfStr += '};'
                    sscanfStr += 'void* values[' + str(len(idList)) + '] = {};'
                    
                    
                    j = 0
                    local_name = 'tmp_j'
                    while j < len(idList):
                        stri = ''
                        strs = ''
                        if idList[j] in eventParaList:
                            stri = monitorParams[idList[j]+1]['name'] + ';'
                            strs =  '(void*)' + monitorParams[idList[j]+1]['name'] + ';'
                        else:
                            stri = '(atoi(monitor_parameter_val_strs[identity[' + str(j)+']]));'
                            strs = '(void*)monitor_parameter_val_strs[identity[' + str(j)+']];\n'
                        sscanfStr += 'if (target_parameterTypes[identity[' + str(j)+']]==INT) {int '+ local_name + ' = ' + stri
                        sscanfStr += 'values[' + str(j) + '] =(void*)&' + local_name +';}'
                        sscanfStr += 'else if(target_parameterTypes[identity[' + str(j)+']]==STRING) {values[' + str(j)+']=' + strs + '}\n'
                        sscanfStr += 'else {values[' + str(j)+'] = (void *)NULL;}\n'
                        j = j+1
                    
                    
                    #sscanfStr += 'for (int i = 0; i<' + str(len(idList)) + '; i++){\n'
                    
                    
                    #str = '= (atoi(monitor_parameter_val_strs[identity[i]])); values[i]=(void*)&'+local_name+';}\n'
                    #sscanfStr += 'if (target_parameterTypes[identity[i]]==INT) {int '+ local_name + str
                    #sscanfStr += 'else if(target_parameterTypes[identity[i]]==STRING) {values[i]=(void*)monitor_parameter_val_strs[identity[i]];}\n'
                    #sscanfStr += 'else {values[i] = (void *)NULL;}\n'
                    #sscanfStr += '}\n'
                    sscanfStr += 'record = get_%s_monitors_by_identities(identity,'  % (obj.lower())
                    sscanfStr +=  type + ',values'
                    sscanfStr += ',' + str(len(idList)) + ');\n'
                    
                    if targetEvent.creation != None:
                        sscanfStr += 'if(record == NULL){\n'
                        sscanfStr += 'record = (%sMonitorRecord *)malloc(sizeof(%sMonitorRecord));\n' %(obj.title(), obj.title())
                        sscanfStr += '%sData *d = (%sData *)malloc(sizeof(%sData));\n' %(obj.title(),obj.title(),obj.title())
                        #['  %s %s;' % (v['c_type'], v['name']) for v in identities]
                        j = 0
                        for v in identities:
                            sscanfStr += 'if (target_parameterTypes[identity['+str(j)+']]==INT){\n'
                            sscanfStr += '\t d ->' + v['name'] + '=' + '*(int*)values[' + str(j) + '];}\n'
                            sscanfStr += 'else if(target_parameterTypes[identity['+str(j)+']]==STRING) {\t d ->' + v['name'] + '=(void*)' + 'values[' + str(j)+ '];}\n'
                            sscanfStr += 'else {\t d ->' + v['name'] + '= (void *)NULL;}\n'
                        
                            #sscanfStr += 'for (int i = 0; i<' + str(len(idList)) + '; i++){\n'
                            #sscanfStr += 'if (identity[i] ==' + str(j) + '){\n'
                            #sscanfStr += 'if (target_parameterTypes[identity[i]]==INT){int '+ local_name+ '= (atoi(monitor_parameter_val_strs[identity[i]])); ' + '\t d ->' + v['name'] + '=' + local_name+';}\n'#'(void*)&'+local_name+';}\n'
                            #sscanfStr += 'else if(target_parameterTypes[identity[i]]==STRING) {\t d ->' + v['name'] + '=(void*)monitor_parameter_val_strs[identity[i]];}\n'
                            #sscanfStr += 'else {\t d ->' + v['name'] + '= (void *)NULL;}\n'
                            #sscanfStr += '\t}\n\t'
                            j = j+1
                        sscanfStr += CTemplater._addDataString('d',state_vars)
                        #sscanfStr += '\t}\n\t'
                        # mon_init_handler.append('%sMonitor *tempMon = init_%s_monitor(%s);\n' % (obj.title(),obj.lower(),implicit_data_name))
                        sscanfStr += '%sMonitor* tempMon = init_%s_monitor(d);\n' % (obj.title(),obj.lower())
                        sscanfStr += 'tempMon -> send_conn = send_conn;\n'
                        sscanfStr += 'tempMon -> amqp_exchange = amqp_exchange;\n'
                        
                        sscanfStr += 'record -> monitor = tempMon;'
                        sscanfStr += 'record -> next = NULL;'
                        sscanfStr += '}\n\t'
                sscanfStr +=  'while(record != NULL){\n'
                sscanfStr += obj.lower() + '_' + conn.targetEvent + '(record->monitor' + retAttrs + ');\n\t'
                sscanfStr += 'record = record->next;\n\t'
                sscanfStr += '}'
                    

                #retAttrs += ', pro'
                #sscanfStr += obj.lower() + '_' + conn.targetEvent + '(monitor' + retAttrs + ');\n\t'
                sscanfStr += ('printf("%s_%s called.\\n");') % (obj.lower(), conn.targetEvent)
                while index > 1 :
                    sscanfStr+= '}\n\t'
                    index = index - 1

                msg_handler.append(json_string)
                msg_handler.append(sscanfStr)
                #print(sscanfStr)
                #print("\\\\\\\\\\\n")
                #msg_handler.append('                        ' + obj.lower() + '_' + conn.targetEvent + '(monitor' + retAttrs + ');')
                #msg_handler.append('                        printf("%s_%s called.\\n");' % (obj.lower(), conn.targetEvent))
                if json_params_mark == 1:
                    msg_handler.append('}\n\t else{\n\t printf("no parameters.\\n");\n\t}')
                msg_handler.append('                }')
                values['event_msg_handlers'].append('\n'.join(msg_handler))
                

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
                monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}]
                index = 0
                for p in mg._symbolTable.get(m, 'params'):
                    monitorParams += [{'name':'v'+str(index),'c_type': CTemplater.convertTypeForC(p['type'])}]
                    index = index + 1
                monitorParams += [{'name':'provenance','c_type': 'cJSON *'}]
            else:
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

                # Jump to next FSM if this one contains no transitions for the current event
                if len(trans_group) == 0:
                    continue

                reference = 'monitor->state[%s_%s_SCENARIO]' % (obj.upper(), key.upper())
                name_reference = "%s_states_names[%s_%s_SCENARIO][monitor->state[%s_%s_SCENARIO]]"%(obj.lower(), obj.upper(), key.upper(), obj.upper(), key.upper())
                eventFunction.append('if (executed_scenarios[%s_%s_SCENARIO]==0) {' % (obj.upper(), key.upper()))
                eventFunction.append('  switch (%s) {' % reference)
                for start_state, transitions in trans_group.items():
                    eventFunction.append(CTemplater._writeCaseTransition(mg, obj, transitions, reference, name_reference, key))
                if mg._implicitErrors:
                    eventFunction.append('    default:')
                    eventFunction.append('      raise_error(\"%s_%s\", %s, \"%s\", \"DEFAULT\");' % (obj.lower(), key, name_reference, m))
                    
                    #  eventFunction.append('      goto exec;') #add at 09/20
                    eventFunction.append('      break;')
                eventFunction.append('  }')
                eventFunction.append('//executed_scenarios[%s_%s_SCENARIO]=1;' % (obj.upper(), key.upper()))
                eventFunction.append('  }')
    #eventFunction.append('exec:') #add at 09/20
            eventFunction.append('executeEvents(monitor);')
            eventFunction.append('}\n\n')

            export_event_sig = None
            cjson_str = '\tcJSON *root; cJSON* fmt; cJSON* prove; \n\t root = cJSON_CreateObject();\n'
            if 'exported_events' == mg._symbolTable.get(m)['type']:
                paramString = obj.title() + "Monitor* monitor " + CTemplater._generateEventParams(mg,m)
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
                    if v['type'] == 'int':
                        sprintf_routing += '.%ld'
                    elif v['type'] == 'string':
                        sprintf_routing += '.%s'
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
                    if v['type'] == 'int':
                        sprintf_routing += ', (long)(*(int*)(monitor->identities['
                    elif v['type'] == 'string':
                        sprintf_routing += ', (char*)((monitor->identities['
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
                eventFunction.append('  send_message(monitor, message, routing_key);')
                eventFunction.append('}\n\n')
            raiseFunction = CTemplater._writeRaiseFunction(mg, m, obj)

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

        out_w = env.get_template('monitor_wrapper.c').render(values)
        if console_output:
            print("--" + filename + "_monitor_wrapper.c--")
            print(out_w)
        else:
            out_w_file = open(os.path.join(dirname, output_dir, basename + '_monitor_wrapper.c'), 'w')
            out_w_file.write(out_w)
            out_w_file.close()
        
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

    #for dynamic instantiation, no need to analyze routing key when building binding keys
    def _getBindingKeys(mg):
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


    def _writeRaiseFunction(mg, event, obj):
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
            output.append('  push_action(&monitor->export_queue, %s_%s_EVENT, ep_head);' % (obj.upper(), event.upper()))
        output.append('}\n\n')
        return {'code':output, 'signature':signature}
