#!/usr/bin/env python
# -*- coding: utf-8 -*-

#-------------------------------------------------------------------------------
# mgen.py
#
# Peter Gebhard (pgeb@seas.upenn.edu)
#-------------------------------------------------------------------------------

from .parser import *
from .fsm import *
from grako.ast import AST
from jinja2 import Environment, PackageLoader
import os
import json
import collections
import re
import shutil
import string
from pathlib import Path
from .architecture import *

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
        self.a4smedlAST = None
        self.monitorInterface = []
        self.archSpec = []
        self.identities = []


    def generate(self, pedlsmedlName, a4smedlName, helper=None):
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
        
        # Parser the architecture, it exists
        if not a4smedlName == None:
            a4smedlPath = Path(a4smedlName + '.a4smedl')
            if a4smedlPath.exists():
                with a4smedlPath.open() as a4smedlFile:
                    a4smedlText = a4smedlFile.read()
                a4smedlPar = a4smedlParser(parseinfo=False,comments_re="(/\*([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/)|(//.*)")
                self.a4smedlAST = a4smedlPar.parse(a4smedlText,'top',filename=a4smedlPath,trace=False,whitespace=None)
                if self._printStructs:
                    print('A4SMEDL AST:')
                    print(self.a4smedlAST)
                    print('\nA4SMEDL JSON:')
                    print(json.dumps(self.a4smedlAST,indent=2))
        
        # Process the SMEDL AST
        self._symbolTable = SmedlSymbolTable()
        self._parseToSymbolTable('top', self.smedlAST)
        self._getParameterNames(self.smedlAST)
        allFSMs = self._generateFSMs(self.smedlAST)
        
        # procss architecture AST
        self._parseArchitecture('top',self.a4smedlAST)
        
        #for mon in self.monitorInterface:
        #    print(mon)
        #    print('\n')
        
        #for pattern in self.archSpec:
        #    print(pattern)
        #    print('\n')
        
        # Output the internal symbol table and FSMs
        if self._printStructs:
            print('\nSMEDL Symbol Table:')
            for k in self._symbolTable:
                print('%s: %s' % (k, self._symbolTable[k]))
            for key, fsm in list(allFSMs.items()):
                print('\nFSM: %s\n' % key)
                print('%s\n' % fsm)

        self._outputToTemplate(allFSMs, pedlsmedlName, helper, self.pedlAST)

    def _parseInter(self,object):
        if isinstance(object, AST):
            for k,v in list(object.items()):
                if k == 'interfaces':
                    if isinstance(v, list):
                        for mon in v:
                            self._makeMonitor(mon)


    def _parseArchitecture(self, label, object):
        if isinstance(object, AST):
            for k, v in list(object.items()):
                if k == 'monitor_declaration':
                    self._parseInter(v)
                elif k == 'archSpec':
                    self._parseSpec(v)



    def _makeMonitor(self,object):
        if isinstance(object,list):
            for mon in object:
                monId = None
                para = []
                imported = []
                exported = []
                montype = None
                for k,v in list(mon.items()):
                    if k == 'mon_type':
                        monType = v
                    elif k == 'monitor_identifier':
                        monId = v
                    elif k == 'params':
                        if not v == None:
                            para = v
                    elif k == 'imported_events':
                        imported = self._makeEventList(v)
                    elif k == 'exported_events':
                        #print('exported')
                        exported = self._makeEventList(v)
                            #print(v)
                interface = Interface(monType,monId,para,imported,exported)
                #print(interface)
                self.monitorInterface.append(interface)

    def _makeEventList(self,object):
        lst = []
        if object == None:
            return lst
        if isinstance(object,list):
            for events in object:
                if isinstance(events,list):
                    for ev in events:
                        if isinstance(ev,AST):
                            err = None
                            ev_id = None
                            para = []
                            for k,v in list(ev.items()):
                                if k == 'error':
                                    err = v
                                elif k == 'event_id':
                                    ev_id = v
                                elif k == 'params' :
                                    if v == None :
                                        para = []
                                    elif isinstance(v,list):
                                        para = v
                                    elif isinstance(v,str):
                                            para = [v]
                            event = Event(err,ev_id,para)
                            lst.append(event)
                elif isinstance(events,AST):
                    err = None
                    ev_id = None
                    para = []
                    for k,v in list(events.items()):
                        if k == 'error':
                            err = v
                        elif k == 'event_id':
                            ev_id = v
                        elif k == 'params' :
                            if v == None :
                                para = []
                            elif isinstance(v,list):
                                para = v
                            elif isinstance(v,str):
                                para = [v]
                    event = Event(err,ev_id,para)
                    lst.append(event)

        return lst

    def _parseSpec(self,object):
        if isinstance(object, AST):
            
            for k,v in list(object.items()):
                if k == 'conn_expr':
                    #print(v)
                    #print('\n')
                    if isinstance(v, list):
                        #i = 0
                        for conn in v:
                            #print(i)
                            self._makeConnExpr(conn)
    

    def _makeConnExpr(self,object):
        if isinstance(object, AST):
            
            conn_name = None
            s_i = None
            t_i = None
            t_e = None
            for k,v in list(object.items()):
                if k == 'connection':
                    conn_name = v
                elif k == 'source_machine_identifier':
                    s_i = v
                elif k == 'source_event_identifier':
                    s_e == v
                elif k == 'target_machine_identifier':
                    t_i = v
                elif k == 'target_event_identifier':
                    t_e = v
                elif k == 'pattern_spec':
                    pa_spec = self._makePatternSpec(v)
            if conn_name == None:
                conn_name = s_i + '_' + s_e
            if not self._checkConnExprDef(s_i,s_e,t_i,t_e):
                raise ValueError('attributes of events do not match')
            connEx = ConnectionExpr(s_i,s_e,t_i,t_e,pa_spec)
            #print(connEx)
            self.archSpec.append(connEx)
        elif isinstance(object,list):
            conn_name = None
            s_i = None
            t_i = None
            t_e = None
            for obj in object:
                for k,v in list(obj.items()):
                    pa_spec = []
                    if k == 'connection':
                        conn_name = v
                    elif k == 'source_machine_identifier':
                        s_i = v
                    elif k == 'source_event_identifier':
                        s_e = v
                    elif k == 'target_machine_identifier':
                        t_i = v
                    elif k == 'target_event_identifier':
                        t_e = v
                    elif k == 'pattern_spec':
                        pa_spec = self._makePatternSpec(v)
                if conn_name == None:
                    conn_name = s_i + '_'+s_e
            #TODO:match number of attributes of the source and target events
                if not self._checkConnExprDef(s_i,s_e,t_i,t_e):
                    raise ValueError('attributes of events do not match')
                connEx = ConnectionExpr(conn_name,s_i,s_e,t_i,t_e,pa_spec)
                #print(connEx)
                self.archSpec.append(connEx)

    def _makePatternSpec(self,object):
        lst = []
        if object == None:
            return lst
        if isinstance(object,AST):
            lt = None
            li = -1
            rt = None
            ri = -1
            for k,v in list(object.items()):
                if k == 'left':
                    for kk,vv in list(v.items()):
                        if kk == 'term_id':
                            lt = vv
                        elif kk == 'term_index':
                            li = int(vv)
                elif k == 'operator':
                    op = v
                elif k == 'right' :
                    for kk,vv in list(v.items()):
                        if kk == 'term_id':
                            rt = vv
                        elif kk == 'term_index':
                            ri = int(vv)
            spec = PatternExpr()
            spec.addOperator(op)
            spec.addTerm(lt,li,rt,ri)
            lst.append(spec)

        elif isinstance(object,list):
            lt = None
            li = -1
            rt = None
            ri = -1
            for event in object:
                for k,v in list(event.items()):
                    if k == 'left':
                        for kk,vv in list(v.items()):
                            if kk == 'term_id':
                                lt = vv
                            elif kk == 'term_index':
                                li = int(vv)
                    elif k == 'operator':
                        op = v
                    elif k == 'right' :
                        for kk,vv in list(v.items()):
                            if kk == 'term_id':
                                rt = vv
                            elif kk == 'term_index':
                                ri = int(vv)
                spec = PatternExpr()
                spec.addOperator(op)
                spec.addTerm(lt,li,rt,ri)
                lst.append(spec)
        
        return lst

    def _checkConnExprDef(self,si,se,ti,te):
        left_mon = None
        left_ev = None
        right_mon = None
        right_ev = None
        for mon in self.monitorInterface:
            if si == mon.id:
                for ev in mon.exportedEvents:
                    if ev.event_id == se:
                        left_ev = ev.params
                        break
                left_mon = mon
            elif ti == mon.id:
                for ev in mon.importedEvents:
                    if ev.event_id == se:
                        right_ev = ev.params
                        break
                right_mon = mon
        if left_mon == None or right_mon == None or not left_ev == right_ev:
            return False
        return True

    def _checkBound(self,conn,term,index):
        if term == conn.sourceMachine or term == conn.targetMachine:
            for mon in self.monitorInterface:
                if term == mon.id:
                    if index < len(mon.params):
                        return True
            return False
        else:
            #term must be in sourceMachine.exported events
            for mon in self.monitorInterface:
                if conn.sourceMachine == mon.id:
                    for ev in  mon.exportedEvents:
                        if ev.event_id == term:
                            if index < len(ev.params):
                                return True
            return False

    def _getBindingKeysNum(self):
        num = 0
        name = self._symbolTable.getSymbolsByType('object')[0]
        for conn in self.archSpec:
            if name==conn.targetMachine:
                num=num+1
        return num

    def _getMachine(self,name):
        for mon in self.monitorInterface:
            if name == mon.id:
                return mon
        return None

    def _getSourceEvent(self,machine,event):
        for mon in self.monitorInterface:
            if machine == mon.id:
                for ev in  mon.exportedEvents:
                    if ev.event_id == event:
                            return ev
        return None

    def _getIdentityName(self,index):
        id = 0
        for name in self.identities:
            if id == index:
                return name
            id = id + 1
        return None
    
    def _getBindingKeys(self):
        lst = []
        name = self._symbolTable.getSymbolsByType('object')[0]
        #print(name)
        k = 0
        for conn in self.archSpec:
            b_str = 'bindingkeys['+str(k)+']'
            if name==conn.targetMachine:
                
                p_str = b_str + '=(char*)malloc(255*sizeof(char));\n'+'\tstrcpy('+b_str+',"'+conn.connName+'");\n'
                sourceMachine = self._getMachine(conn.sourceMachine)
                if sourceMachine == None:
                    raise ValueError('source machine not exist')
                sourceEvent = self._getSourceEvent(conn.sourceMachine,conn.sourceEvent)
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
                            if self._checkBound(conn,leftterm,leftindex) and self._checkBound(conn,rightterm,rightindex):
                                if leftterm == conn.targetMachine:
                                    val = self._getIdentityName(leftindex)
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


    def _parseToSymbolTable(self, label, object):
        if isinstance(object, AST):
            for k, v in list(object.items()):
                if k == 'object':
                    self._symbolTable.add(v, {'type': 'object'})
                elif label == 'identity' and k == 'var':
                    if isinstance(v, list):
                        for var in v:
                            self._symbolTable.add(var, {'type': 'identity', 'datatype': object['type']})
                            self.identities.append(var)
                    else:
                        self._symbolTable.add(v, {'type': 'identity', 'datatype': object['type']})
                        self.identities.append(v)
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


    def _outputToTemplate(self, allFSMs, filename, helper, pedlAST):
        if self._debug:
            if pedlAST:
                print("Target Monitor Points: " + pedlAST.getTargetMonitorPoints())
        obj = self._symbolTable.getSymbolsByType('object')[0]
        state_vars = [{'type': self._symbolTable.get(v)['datatype'], 'name': v} for v in self._symbolTable.getSymbolsByType('state')]
        for s in state_vars:
            s['c_type'] = self._convertTypeForC(s['type'])

        # If there are no identities defined, make a default one:
        if len(self._symbolTable.getSymbolsByType('identity')) == 0:
            identities = [{'type': 'opaque', 'name': 'id'}]
        else:
            identities = [{'type': self._symbolTable.get(v)['datatype'], 'name': v} for v in self._symbolTable.getSymbolsByType('identity')]
        for id in identities:
            id['c_type'] = self._convertTypeForC(id['type'])

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

        events = ['%s_%s_EVENT' % (obj.upper(), str(e).upper()) for e in self._symbolTable.getEvents()]
        values['event_enums'] = ', '.join(events)
        errors = ['%s_DEFAULT' % obj.upper()]
        for e in self._symbolTable.getSymbolsByType('event'):
            if self._symbolTable[e]['error']:
                errors.append('%s_%s_EVENT' % (obj.upper, e.upper()))
        values['error_enums'] = ', '.join(errors)

        values['add_to_map_calls'] = ['add_%s_monitor_to_map(monitor, %s)' % (obj.lower(), i) for i in values['identities_names']]

        # Output a method for each event (switch statement to handle FSM transitions)
        methods = self._symbolTable.getEvents()
        callCases = []
        values['signatures']= []
        values['event_code'] = []
        values['event_msg_handlers'] = []
        if self._getBindingKeysNum() == 0:
            values['bindingkeys_num'] = 1 # TODO: Make these customizable
        else:
            values['bindingkeys_num'] = self._getBindingKeysNum()# TODO: Make these customizable

        values['b_keys'] = self._getBindingKeys()

        #construct event_msg_handlers
        
        name = self._symbolTable.getSymbolsByType('object')[0]
        for conn in self.archSpec:
            if conn.targetMachine == name:
                monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                [{'name': p['name'], 'c_type': self._convertTypeForC(p['type'])} for p in self._symbolTable.get(conn.targetEvent, 'params')]
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
            if 'imported_events' == self._symbolTable.get(m)['type'] and pedlAST is not None:
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

            if self._debug:
                print(m)
                print(self._symbolTable.get(m, 'params'))

            monitorParams = [{'name':'monitor', 'c_type':obj.title() + 'Monitor*'}] + \
                [{'name': p['name'], 'c_type': self._convertTypeForC(p['type'])} for p in self._symbolTable.get(m, 'params')]

            if 'exported_events' != self._symbolTable.get(m)['type']:
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
                        eventFunction.append(self._writeCaseTransition(obj, transitions, reference, name_reference, key))
                    if self._implicitErrors:
                        eventFunction.append('    default:')
                        eventFunction.append('      raise_error(\"%s_%s\", %s, \"%s\", \"DEFAULT\");'%(obj.lower(), key, name_reference, m))
                        eventFunction.append('      break;')
                    eventFunction.append('  }')
                eventFunction.append('}')

                # Build event message handler block for incoming RabbitMQ messages
                #msg_handler = []
                #if len(values['event_msg_handlers']) == 0:
                #    cond = 'if'
                #else:
                #    cond = '                else if'
                #msg_handler.append(cond + ' (!strcmp(eventName,"%s_%s")) {' % (obj.lower(), m))
                #sscanfStr = '%s'
                #sscanfAttrs = 'e'
                #retAttrs = ''
                #for p in monitorParams[1:]:
                #    msg_handler.append('                    %s %s = 0;' % (p['c_type'], p['name']))
                #    if p['c_type'] == 'int':
                #       sscanfStr += ' %d'
                #   elif p['c_type'] == 'char':
                #        sscanfStr += ' %s'
                #    elif p['c_type'] == 'float':
                #        exit("this should never happen. there is a missing float->double conversion.")
                #   elif p['c_type'] == 'double':
                #       sscanfStr += ' %lf'
                #   sscanfAttrs += ', &' + p['name']
                #   retAttrs += ', ' + p['name']
                #msg_handler.append('                    int ret = sscanf(string, "' + sscanfStr + '", ' + sscanfAttrs + ');')
                #msg_handler.append('                    if (ret == ' + str(len(monitorParams)) + ') {')
                #msg_handler.append('                        ' + obj.lower() + '_' + m + '(monitor' + retAttrs + ');')
                #msg_handler.append('                        printf("%s_%s called.\\n");' % (obj.lower(), m))
                #msg_handler.append('                    }')
                #msg_handler.append('                }')
                #values['event_msg_handlers'].append('\n'.join(msg_handler))

            raiseFunction = self._writeRaiseFunction(m, obj)

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
                values['event_code'].append(self._updateVarNames({'event':eventFunction, 'probe':probeFunction, 'raise':raiseFunction['code']}, m))
            else:
                values['event_code'].append(self._updateVarNames({'event':eventFunction, 'raise':raiseFunction['code']}, m))

            values['signatures'].append(raiseFunction['signature'])

            callCases.append(self._writeCallCase(m))

        # Render the monitor templates and write to disk
        env = Environment(loader=PackageLoader('smedl'))

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
    def _convertTypeForC(self, smedlType):
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


    def _updateVarNames(self, funcs, method):
        out = {}
        for name, func in funcs.items():
            tmp = func
            for p in self._symbolTable.get(method, 'params'):
                out_s = []
                for s in tmp:
                    out_s.append(re.sub(r'\b' + p['true_name'] + r'\b', p['name'], s))
                tmp = out_s
            out[name] = tmp
        return out

    # Write out the switch statement case for a SMEDL trace transition
    def _writeCaseTransition(self, obj, transitions, currentState, stateName, scenario):
        output = ['    case %s_%s_%s:\n' % (obj.upper(), scenario.upper(), transitions[0].startState.name.upper())]

        if self._debug:
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
                        output.append('        %s\n' % self._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                output.append('      }\n')
            elif len(transitions) == 1:
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % self._writeAction(obj, action))
                output.append('      %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                break
            elif transitions[i].guard:
                output.append('      else if(' + transitions[i].guard.replace('this.', 'monitor->') + ') {\n')
                if transitions[i].nextActions:
                    for action in transitions[i].nextActions:
                        output.append('        %s\n' % self._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].nextState.name)).upper() + ';\n')
                output.append('      }\n')

            # Handle Else (an Else state is defined, or reaching an Else denotes an error condition)
            if transitions[i].elseState and ((i+1 < len(transitions) and transitions[i+1].guard is None) or i+1 == len(transitions)):
                output.append('      else {\n')
                if transitions[i].elseActions:
                    for action in transitions[i].elseActions:
                        output.append('        %s\n' % self._writeAction(obj, action))
                output.append('        %s = ' % currentState + ("%s_%s_%s" % (obj, scenario, transitions[i].elseState.name)).upper() + ';\n')
                output.append('      }\n')
            elif self._implicitErrors and i == len(transitions)-1:
                output.append('      else {\n')
                output.append('        raise_error(\"%s\", %s, \"%s\", \"DEFAULT\");\n' % (scenario, stateName, currentState))
                output.append('      }\n')
        output.append('      break;\n')
        return "".join(output)


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


    def _getEventParams(self, paramString):
        paramsList = []
        params = [str(s) for s in paramString.split(', ')]
        for p in params:
            paramsList.append([str(s) for s in p.split(' ')])
        return paramsList


    def _writeCallCase(self, event):
        output = []
        output.append('    case %s: ;' % event.upper())
        paramString = ','.join(['%s %s'%(p['type'], p['name']) for p in self._symbolTable.get(event, 'params')])
        if paramString == '':
            output.append('      %s(monitor);' % event)
        else:
            params = self._getEventParams(paramString)
            for p in params:
                output.append('      %s %s_%s = monitor->action_queue->params->%c;' % (p[0], p[1], event, p[0][0]))
                output.append('      pop_param(&monitor->action_queue->params);')
            callParams = ", ".join('%s_%s' % (p[1], event) for p in params)
            output.append('      %s(%s);' % (event, ", ".join(['monitor', callParams])))
        output.append('      break;')
        return '\n'.join(output)


    def _writeRaiseFunction(self, event, obj):
        paramString = ', '.join(['%s %s'%(self._convertTypeForC(p['type']), p['name']) for p in self._symbolTable.get(event, 'params')])
        if len(paramString) > 0:
            paramString = obj.title() + "Monitor* monitor, " + paramString
        else:
            paramString = obj.title() + "Monitor* monitor"
        output = []
        signature = 'void raise_%s_%s(%s)' % (obj.lower(), event, paramString)
        output.append(signature + ' {')
        output.append('  param *p_head = NULL;')
        if len(paramString) > 0:
            for p in self._getEventParams(paramString):
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

        if 'exported_events' == self._symbolTable.get(event)['type']:
            output.append('  char message[256];')
            sprintf = '  sprintf(message, "%s_%s' % (obj.lower(), event)
            evParams = self._getEventParams(paramString)[1:]
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
            name = self._symbolTable.getSymbolsByType('object')[0]
            connName = None
            for conn in self.archSpec:
                if conn.sourceMachine == name and conn.sourceEvent == event:
                    connName = conn.connName
                    break

            if connName == None:
                connName = obj+'_'+ event
            sprintf_routing = '  sprintf(routing_key, "%s' % (connName)
            # TODO: peter, write functions for printing and parsing monitor identities
            # this cast is broken and wrong, but works as long as we have only one monitor process
            for v in self.identities:
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
            for v in self.identities:
                print(v)
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
            #return [{'type':types[i], 'true_name':names[i], 'name':'mon_var_'+names[i]} for i in range(len(names))]
        return [{'type':types[i], 'true_name':names[i], 'name':names[i]} for i in range(len(names))]


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
        return self._removeParentheses(exprStr)


    def _addMonitorArrowToStateVariables(self, string):
        for sv in self._symbolTable.getSymbolsByType('state'):
            indices = [t.start() for t in re.finditer(sv, string)]
            for index in indices:
                if string[index-5:index] != 'this.' and string[index-9:index] != 'monitor->':  # Prevent duplicated 'this.'
                    string = string[:index] + 'monitor->' + string[index:]
        return string


    def _removeParentheses(self, guard):
        if guard.startswith('(') and guard.endswith(')'):
            stack = ['s']
            for ch in guard[1:-1]:
                if ch == '(':
                    stack.append('(')
                if ch == ')':
                    stack.pop()
            if len(stack) == 1 and stack[0] == 's':
                return self._removeParentheses(guard[1:-1])
            else:
                return guard
        else:
            return guard


    def _checkReferences(self, guard):
        re.findall(r'\s([A-Za-z_]\w*).\w+\W+', guard)


import argparse

def main():
    parser = argparse.ArgumentParser(description="Code Generator for SMEDL and PEDL.")
    parser.add_argument('--helper', help='Include header file for helper functions')
    parser.add_argument('-s', '--structs', help='Print internal data structures', action='store_true')
    parser.add_argument('-d', '--debug', help='Show debug output', action='store_true')
    parser.add_argument('-e', '--noimplicit', help='Disable implicit error handling in generated monitor', action='store_false')
    # TODO: Add version flag
    parser.add_argument('pedlsmedl', metavar="pedl_smedl_filename", help="the name of the PEDL and SMEDL files to parse")
    parser.add_argument('--arch', type = str, metavar="a4smedl_filename", help="the name of architechture file to parse")
    args = parser.parse_args()

    mgen = MonitorGenerator(structs=args.structs, debug=args.debug, implicit=args.noimplicit)
    mgen.generate(args.pedlsmedl, args.arch, helper=args.helper)

if __name__ == '__main__':
    main()
