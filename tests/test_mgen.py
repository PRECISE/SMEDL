from smedl_parser import smedlParser
from smedl_symboltable import smedlSymbolTable
import json
import unittest
import smedlgen


class TestSmedlgen(unittest.TestCase):

    def setUp(self):
        self.writer = SmedlWriter("SafeMon")
        self.writer.add_i("opaque id")
        self.writer.add_st("int upbound, lobound")
        self.writer.add_e("imported updatePos(int), changeDir")
        self.writer.add_sc("sc1")
        self.writer.add_t("sc1", "SafeMon -> updatePos(pos) when pos == upbound || pos == lobound -> Switch")
        self.writer.add_t("sc1", "Switch -> changeDir() -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() -> SafeMon")
        self.make_ast()
        # print(self.ast)

    def test_parseToSymbolTable(self):
        symbolTable = smedlSymbolTable()
        smedlgen.parseToSymbolTable('top', self.ast, symbolTable)
        self.assertEqual('int', symbolTable['lobound']['datatype'])
        self.assertEqual('state', symbolTable['upbound']['type'])
        self.assertEqual('event', symbolTable['updatePos']['type'])
        self.assertEqual('scenarios', symbolTable['sc1']['type'])
        self.assertEqual('trace_state', symbolTable['SafeMon']['type'])
        self.assertEqual('trace_state', symbolTable['Switch']['type'])
        # print(symbolTable)

    def test_generateFSM(self):
        symbolTable = smedlSymbolTable()
        smedlgen.parseToSymbolTable('top', self.ast, symbolTable)
        fsm = next(iter(list(smedlgen.generateFSMs(self.ast, symbolTable).values())))
        # print(type(fsm))
        self.assertEqual(2, len(fsm.states))
        self.assertEqual(3, len(fsm.transitions))
        self.assertTrue(fsm.stateExists('SafeMon'))
        self.assertTrue(fsm.stateExists('Switch'))
        updatePos = fsm.getTransitionsByEvent('updatePos')
        self.assertEqual(1, len(updatePos))
        self.assertEqual('SafeMon', updatePos[0].start.name)
        self.assertEqual('pos == upbound || pos == lobound', updatePos[0].guard)
        changeDir = fsm.getTransitionsByAction('changeDir')
        self.assertEqual(2, len(changeDir))
        # print(fsm)

    def test_findFunctionParams(self):
        trace = self.ast['scenarios'][0][0]['traces'][0]['trace_step'][1]['step_event']['expression']
        params = trace['trailer']['params']
        param_names = str(smedlgen.findFunctionParams(trace['atom'], params, self.ast))
        self.assertEqual('int pos', param_names)
        trace = self.ast['scenarios'][0][0]['traces'][1]['trace_step'][1]['step_event']['expression']
        params = trace['trailer']['params']
        param_names = str(smedlgen.findFunctionParams(trace['atom'], params, self.ast))
        self.assertEqual('', param_names)
        self.writer.add_t("sc1", "SafeMon -> updatePos() -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> updatePos(pos, pos2) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir(pos, pos2) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> newOne() -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> newOne(x, y, z) -> SafeMon")
        self.make_ast()
        trace = self.ast['scenarios'][0][0]['traces'][3]['trace_step'][1]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, smedlgen.findFunctionParams, trace['atom'], params, self.ast)
        trace = self.ast['scenarios'][0][0]['traces'][4]['trace_step'][1]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, smedlgen.findFunctionParams, trace['atom'], params, self.ast)
        trace = self.ast['scenarios'][0][0]['traces'][5]['trace_step'][1]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, smedlgen.findFunctionParams, trace['atom'], params, self.ast)
        trace = self.ast['scenarios'][0][0]['traces'][6]['trace_step'][1]['step_event']['expression']
        params = trace['trailer']['params']
        self.assertRaises(ValueError, smedlgen.findFunctionParams, trace['atom'], params, self.ast)
        self.writer.add_e("exported other(int), newOne(int)")
        self.make_ast()
        self.assertRaises(ValueError, smedlgen.findFunctionParams, trace['atom'], params, self.ast)
        self.writer.rm_e(1)
        self.writer.add_e("exported other(int), newOne(int, float, bool)")
        self.make_ast()
        trace = self.ast['scenarios'][0][0]['traces'][7]['trace_step'][1]['step_event']['expression']
        params = trace['trailer']['params']
        param_names = smedlgen.findFunctionParams(trace['atom'], params, self.ast)
        # print(trace['atom'] + "(" + param_names + ")")

    def test_getParamTypes(self):
        self.writer.add_e("exported newOne(int, int, bool, float)")
        self.make_ast()
        events = self.ast['imported_events'][0]
        types = smedlgen.getParamTypes('updatePos', events)
        self.assertEqual(1, len(types))
        self.assertEqual('int', types[0])
        types = smedlgen.getParamTypes('changeDir', events)
        self.assertTrue(isinstance(types, list))
        self.assertEqual(0, len(types))
        types = smedlgen.getParamTypes('doesntExist', events)
        self.assertTrue(types is None)
        types = smedlgen.getParamTypes('newOne', events)
        self.assertTrue(types is None)
        events = self.ast['exported_events'][0]
        types = smedlgen.getParamTypes('updatePos', events)
        self.assertTrue(types is None)
        types = smedlgen.getParamTypes('changeDir', events)
        self.assertTrue(types is None)
        types = smedlgen.getParamTypes('newOne', events)
        self.assertEqual(4, len(types))
        self.assertEqual('int', types[0])
        self.assertEqual('int', types[1])
        self.assertEqual('bool', types[2])
        self.assertEqual('float', types[3])
        # print(json.dumps(events, indent=2))

    def test_formatGuard(self):
        self.writer.add_t("sc1", "SafeMon -> changeDir() when ((+-~~+-~~5)) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when +arr[5 + fn(6)] -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing.thing2[5] == 6 -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing % 5 == 6 && true || x + 5 == null -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when ((x == 5 || true || y(x)) && z > 3 || b < c) && d -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when !(a < b) && !c || !!!!(d + e) || f < !!!g -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when !(a < b) && !c || !!!!!(d + e) || f < !!!g -> SafeMon")
        self.make_ast()
        # print(json.dumps(self.ast, indent=2))
        term = self.ast['scenarios'][0][0]['traces'][3]['trace_step'][1]['step_event']['when']
        self.assertEqual("+-~~+-~~5", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][4]['trace_step'][1]['step_event']['when']
        self.assertEqual("+arr[5 + fn(6)]", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][5]['trace_step'][1]['step_event']['when']
        self.assertEqual("obj.thing.thing2[5] == 6", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][6]['trace_step'][1]['step_event']['when']
        self.assertEqual("(obj.thing % 5 == 6 && true) || x + 5 == null", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][7]['trace_step'][1]['step_event']['when']
        self.assertEqual("(((x == 5 || true || y(x)) && z > 3) || b < c) && d", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][8]['trace_step'][1]['step_event']['when']
        self.assertEqual("(!(a < b) && !c) || d + e || f < !!!g", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][9]['trace_step'][1]['step_event']['when']
        self.assertEqual("(!(a < b) && !c) || !(d + e) || f < !!!g", smedlgen.formatGuard(term))

    def test_addThisDotToStateVariables(self): #TODO
        smedlFilename = "testcases/pqueue/c/smedl/pqueue.smedl"
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
        symbolTable = smedlSymbolTable()
        smedlgen.parseToSymbolTable('top', ast, symbolTable)


        self.writer.add_t("sc1", "SafeMon -> changeDir() when ((+-~~+-~~5)) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when +arr[5 + fn(6)] -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing.thing2[5] == 6 -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing % 5 == 6 && true || x + 5 == null -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when ((x == 5 || true || y(x)) && z > 3 || b < c) && d -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when !(a < b) && !c || !!!!(d + e) || f < !!!g -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when !(a < b) && !c || !!!!!(d + e) || f < !!!g -> SafeMon")
        self.make_ast()
        # print(json.dumps(self.ast, indent=2))
        term = self.ast['scenarios'][0][0]['traces'][3]['trace_step'][1]['step_event']['when']
        self.assertEqual("+-~~+-~~5", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][4]['trace_step'][1]['step_event']['when']
        self.assertEqual("+arr[5 + fn(6)]", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][5]['trace_step'][1]['step_event']['when']
        self.assertEqual("obj.thing.thing2[5] == 6", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][6]['trace_step'][1]['step_event']['when']
        self.assertEqual("(obj.thing % 5 == 6 && true) || x + 5 == null", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][7]['trace_step'][1]['step_event']['when']
        self.assertEqual("(((x == 5 || true || y(x)) && z > 3) || b < c) && d", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][8]['trace_step'][1]['step_event']['when']
        self.assertEqual("(!(a < b) && !c) || d + e || f < !!!g", smedlgen.formatGuard(term))
        term = self.ast['scenarios'][0][0]['traces'][9]['trace_step'][1]['step_event']['when']
        self.assertEqual("(!(a < b) && !c) || !(d + e) || f < !!!g", smedlgen.formatGuard(term))

    def test_guardToString(self):
        self.writer.add_t("sc1", "SafeMon -> changeDir() when 5 -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when +5 -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when +-~~+-~~5 -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when -fn(-5 + 5) -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when +arr[5 + fn(6)] -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing.thing2[5] == 6 -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when obj.thing % 5 == 6 && true || x + 5 == null -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when ((x == 5 || true || y(x)) && z > 3 || b < c) && d -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when fn(helper(2) * 3) == -x(5, 6)  -> SafeMon")
        self.writer.add_t("sc1", "SafeMon -> changeDir() when 4 * (5 + 6) == 7 -> SafeMon")
        self.make_ast()
        term = self.ast['scenarios'][0][0]['traces'][3]['trace_step'][1]['step_event']['when']
        self.assertEqual("5", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][4]['trace_step'][1]['step_event']['when']
        self.assertEqual("+5", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][5]['trace_step'][1]['step_event']['when']
        self.assertEqual("+-~~+-~~5", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][6]['trace_step'][1]['step_event']['when']
        self.assertEqual("-fn(-5 + 5)", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][7]['trace_step'][1]['step_event']['when']
        self.assertEqual("+arr[5 + fn(6)]", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][8]['trace_step'][1]['step_event']['when']
        self.assertEqual("obj.thing.thing2[5] == 6", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][9]['trace_step'][1]['step_event']['when']
        self.assertEqual("((obj.thing % 5 == 6 && true) || x + 5 == null)", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][10]['trace_step'][1]['step_event']['when']
        self.assertEqual("((((x == 5 || true || y(x)) && z > 3) || b < c) && d)", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][11]['trace_step'][1]['step_event']['when']
        self.assertEqual("fn(helper(2) * 3) == -x(5, 6)", smedlgen.guardToString(term))
        term = self.ast['scenarios'][0][0]['traces'][12]['trace_step'][1]['step_event']['when']
        self.assertEqual("4 * (5 + 6) == 7", smedlgen.guardToString(term))
        # print(json.dumps(term, indent=2))

    def test_termToString(self):
        self.writer.add_t("sc1", "SafeMon -> changeDir() when fn(helper(2) * 3) == -x(5)  -> SafeMon")
        self.make_ast()
        term = self.ast['scenarios'][0][0]['traces'][3]['trace_step'][1]['step_event']['when']['comp'][0]
        self.assertEqual("fn(helper(2) * 3)", smedlgen.termToString(term))
        term = self.ast['scenarios'][0][0]['traces'][3]['trace_step'][1]['step_event']['when']['comp'][1]
        self.assertEqual("-x(5)", smedlgen.termToString(term))

    def test_removeParentheses(self):
        self.assertEqual("x", smedlgen.removeParentheses("(x)"))
        self.assertEqual("()(x)", smedlgen.removeParentheses("()(x)"))
        self.assertEqual("(y) + ((x + 2))", smedlgen.removeParentheses("(((y) + ((x + 2))))"))

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
