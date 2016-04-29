from utils import setup_syspath; setup_syspath()
from smedl.parser.smedl_parser import smedlParser
from smedl.parser.smedl_symboltable import SmedlSymbolTable
from smedl.mgen import MonitorGenerator
import json
import unittest

class TestMGen(unittest.TestCase):

    def setUp(self):
        self.writer = SmedlWriter("SafeMonObj")
        self.writer.add_i("opaque id")
        self.writer.add_st("int upbound, lobound")
        self.writer.add_e("imported updatePos(int), changeDir")
        self.writer.add_sc("sc1")
        self.writer.add_t("sc1", "SafeMon -> updatePos(pos) when pos == upbound || pos == lobound -> Switch")
        self.writer.add_t("sc1", "Switch -> changeDir() -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() -> SafeMon")
        self.make_ast()
        self.monitor = MonitorGenerator()
        # print(self.ast)

    def test_parseToSymbolTable(self):
        self.monitor._parseToSymbolTable('top', self.ast)
        self.assertEqual('int', self.monitor._symbolTable['lobound']['datatype'])
        self.assertEqual('state', self.monitor._symbolTable['upbound']['type'])
        self.assertEqual('imported_events', self.monitor._symbolTable['updatePos']['type'])
        self.assertEqual('scenarios', self.monitor._symbolTable['sc1']['type'])
        self.assertEqual('trace_state', self.monitor._symbolTable['SafeMon']['type'])
        self.assertEqual('trace_state', self.monitor._symbolTable['Switch']['type'])
        # print(self.monitor._symbolTable)

    def test_generateFSM(self):
        self.monitor._parseToSymbolTable('top', self.ast)
        fsm = next(iter(list(self.monitor._generateFSMs(self.ast).values())))
        # print(type(fsm))
        self.assertEqual(2, len(fsm.states))
        self.assertEqual(3, len(fsm.transitions))
        self.assertTrue(fsm.stateExists('SafeMon'))
        self.assertTrue(fsm.stateExists('Switch'))
        updatePos = fsm.getTransitionsByEvent('updatePos')
        self.assertEqual(1, len(updatePos))
        self.assertEqual('SafeMon', updatePos[0].startState.name)
        self.assertEqual('pos == this.upbound || pos == this.lobound', updatePos[0].guard)
        changeDir = fsm.getTransitionsByEvent('changeDir')
        self.assertEqual(2, len(changeDir))
        # print(fsm)

    def test_findFunctionParams(self):
        trace = self.ast['scenarios'][0][0]['traces'][0]['trace_steps'][0]['step_event']['expression']
        params = trace['trailer']['params']
        param_names = self.monitor._findFunctionParams(trace['atom'], params, self.ast)
        self.assertEqual('pos', param_names[0]['true_name'])
        trace = self.ast['scenarios'][0][0]['traces'][1]['trace_steps'][0]['step_event']['expression']
        params = trace['trailer']['params']
        param_names = self.monitor._findFunctionParams(trace['atom'], params, self.ast)
        self.assertEqual([], param_names)
        self.writer.add_t("sc1", "SafeMon -> updatePos() -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> updatePos(pos, pos2) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir(pos, pos2) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> newOne() -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> newOne(x, y, z) -> SafeMon")
        self.make_ast()
        trace = self.ast['scenarios'][0][0]['traces'][3]['trace_steps'][0]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, self.monitor._findFunctionParams, trace['atom'], params, self.ast)
        trace = self.ast['scenarios'][0][0]['traces'][4]['trace_steps'][0]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, self.monitor._findFunctionParams, trace['atom'], params, self.ast)
        trace = self.ast['scenarios'][0][0]['traces'][5]['trace_steps'][0]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, self.monitor._findFunctionParams, trace['atom'], params, self.ast)
        trace = self.ast['scenarios'][0][0]['traces'][6]['trace_steps'][0]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, self.monitor._findFunctionParams, trace['atom'], params, self.ast)
        self.writer.add_e("exported other(int), newOne(int)")
        self.make_ast()
        self.assertRaises(ValueError, self.monitor._findFunctionParams, trace['atom'], params, self.ast)
        self.writer.rm_e(1)
        self.writer.add_e("exported other(int), newOne(int, float, bool)")
        self.make_ast()
        trace = self.ast['scenarios'][0][0]['traces'][7]['trace_steps'][0]['step_event']['expression']
        params = trace['trailer']['params']
        param_names = self.monitor._findFunctionParams(trace['atom'], params, self.ast)
        # print(trace['atom'] + "(" + param_names + ")")

    def test_getParamTypes(self):
        self.writer.add_e("exported newOne(int, int, bool, float)")
        self.make_ast()
        events = self.ast['imported_events'][0]
        types = self.monitor._getParamTypes('updatePos', events)
        self.assertEqual(1, len(types))
        self.assertEqual('int', types[0])
        types = self.monitor._getParamTypes('changeDir', events)
        self.assertTrue(isinstance(types, list))
        self.assertEqual(0, len(types))
        types = self.monitor._getParamTypes('doesntExist', events)
        self.assertTrue(types is None)
        types = self.monitor._getParamTypes('newOne', events)
        self.assertTrue(types is None)
        events = self.ast['exported_events'][0]
        types = self.monitor._getParamTypes('updatePos', events)
        self.assertTrue(types is None)
        types = self.monitor._getParamTypes('changeDir', events)
        self.assertTrue(types is None)
        types = self.monitor._getParamTypes('newOne', events)
        self.assertEqual(4, len(types))
        self.assertEqual('int', types[0])
        self.assertEqual('int', types[1])
        self.assertEqual('bool', types[2])
        self.assertEqual('float', types[3])
        # print(json.dumps(events, indent=2))

    def test_formatExpression(self):
        self.writer.add_t("sc1", "SafeMon -> changeDir() when ((+-~~+-~~5)) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when +arr[5 + fn(6)] -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing.thing2[5] == 6 -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing % 5 == 6 && true || x + 5 == null -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when ((x == 5 || true || y(x)) && z > 3 || b < c) && d -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when !(a < b) && !c || !!!!(d + e) || f < !!!g -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when !(a < b) && !c || !!!!!(d + e) || f < !!!g -> SafeMon")
        self.make_ast()
        # print(json.dumps(self.ast, indent=2))
        term = self.ast['scenarios'][0][0]['traces'][3]['trace_steps'][0]['step_event']['when']
        self.assertEqual("+-~~+-~~5", self.monitor._formatExpression(term))
        term = self.ast['scenarios'][0][0]['traces'][4]['trace_steps'][0]['step_event']['when']
        self.assertEqual("+arr[5 + fn(6)]", self.monitor._formatExpression(term))
        term = self.ast['scenarios'][0][0]['traces'][5]['trace_steps'][0]['step_event']['when']
        self.assertEqual("obj.thing.thing2[5] == 6", self.monitor._formatExpression(term))
        term = self.ast['scenarios'][0][0]['traces'][6]['trace_steps'][0]['step_event']['when']
        self.assertEqual("(obj.thing % 5 == 6 && true) || x + 5 == null", self.monitor._formatExpression(term))
        term = self.ast['scenarios'][0][0]['traces'][7]['trace_steps'][0]['step_event']['when']
        self.assertEqual("(((x == 5 || true || y(x)) && z > 3) || b < c) && d", self.monitor._formatExpression(term))
        term = self.ast['scenarios'][0][0]['traces'][8]['trace_steps'][0]['step_event']['when']
        self.assertEqual("(!(a < b) && !c) || d + e || f < !!!g", self.monitor._formatExpression(term))
        term = self.ast['scenarios'][0][0]['traces'][9]['trace_steps'][0]['step_event']['when']
        self.assertEqual("(!(a < b) && !c) || !(d + e) || f < !!!g", self.monitor._formatExpression(term))

    def test_addThisDotToStateVariables(self): #TODO
        smedlFilename = "tests/examples/pqueue/c/smedl/pqueue.smedl"
        with open(smedlFilename) as smedlFile:
            smedlText = smedlFile.read()
        smedlPar = smedlParser(
            parseinfo=False,
            comments_re="(/\*([^*]|[\r\n]|(\*+([^*/]|[\r\n])))*\*+/)|(//.*)")
        ast = smedlPar.parse(
            smedlText,
            'object',
            filename=smedlFilename,
            trace=False,
            whitespace=None)
        self.monitor._parseToSymbolTable('top', ast)
        # TODO: Finish this test

    def test_removeParentheses(self):
        self.assertEqual("x", self.monitor._removeParentheses("(x)"))
        self.assertEqual("()(x)", self.monitor._removeParentheses("()(x)"))
        self.assertEqual("(y) + ((x + 2))", self.monitor._removeParentheses("(((y) + ((x + 2))))"))

    def make_ast(self):
        self.ast = smedlParser(parseinfo=False).parse(self.writer.text,
            'object', filename="test", trace=False, whitespace=None)


class SmedlWriter(object):

    def __init__(self, identifier):
        self.id = identifier
        self.identity = []
        self.state = []
        self.events = []
        self.scenarios = dict()
        self.build()

    def add_i(self, identity):
        self.identity.append(identity)
        self.build()

    def add_st(self, state):
        self.state.append(state)
        self.build()

    def add_e(self, event):
        self.events.append(event)
        self.build()

    def add_sc(self, scenario):
        self.scenarios[scenario] = []
        self.build()

    def add_t(self, scenario, trace):
        self.scenarios[scenario].append(trace)
        self.build()

    def rm_i(self, identity_index):
        del self.identity[identity_index]
        self.build()

    def rm_st(self, state_index):
        del self.state[state_index]
        self.build()

    def rm_e(self, event_index):
        del self.events[event_index]
        self.build()

    def rm_sc(self, scenario):
        self.scenarios.pop(scenario)
        self.build()

    def rm_t(self, scenario, trace_index):
        del self.scenarios[scenario][trace_index]
        self.build()

    def build(self):
        self.text = "object %s\n" % self.id
        if(self.identity):
            self.text += "identity\n"
            for i in self.identity:
                self.text += "\t%s;\n" % i
        if(self.state):
            self.text += "state\n"
            for s in self.state:
                self.text += "\t%s;\n" % s
        if(self.events):
            self.text += "events\n"
            for e in self.events:
                self.text += "\t%s;\n" % e
        if(self.scenarios):
            self.text += "scenarios\n"
            for s in list(self.scenarios.keys()):
                self.text += "\t%s:\n" % s
                for t in self.scenarios[s]:
                    self.text += "\t\t%s\n" % t

if __name__ == '__main__':
    unittest.main()
