from smedl.fsm import FSM, State, Transition
import unittest

class TestFSM(unittest.TestCase):

    def setUp(self):
        self.fsm = FSM()
        self.s1 = State("s1")
        self.s2 = State("s2")
        self.t1 = Transition(self.s1, "SomeEvent", self.s2,
            guard="SomeCondition")
        self.t2 = Transition(self.s2, "SomeOtherEvent", self.s1,
            guard="SomeOtherCondition")

    def test_addState(self):
        self.assertRaises(TypeError, self.fsm.addState, 1)
        self.assertRaises(TypeError, self.fsm.addState, None)
        self.assertRaises(TypeError, self.fsm.addState, dict())
        self.assertRaises(TypeError, self.fsm.addState, "state")
        self.fsm.addState(self.s1)
        self.fsm.addState(self.s2)
        self.assertEqual(2, len(list(self.fsm.states.keys())))
        s1 = self.fsm.states['s1']
        self.assertTrue(isinstance(s1, State))

    def test_deleteState(self):
        self.fsm.addState(self.s1)
        self.fsm.addState(self.s2)
        self.assertEqual(2, len(list(self.fsm.states.keys())))
        self.fsm.deleteState(self.s2)
        self.assertRaises(KeyError, self.fsm.deleteState, self.s2)
        self.assertEqual(1, len(list(self.fsm.states.keys())))
        self.assertTrue(isinstance(self.fsm.states['s1'], State))
        self.assertRaises(KeyError, self.fsm.getStateByName, 's2')

    def test_stateExists(self):
        self.fsm.addState(self.s1)
        self.assertRaises(TypeError, self.fsm.stateExists, 1)
        self.assertRaises(TypeError, self.fsm.stateExists, self.s1)
        self.assertTrue(self.fsm.stateExists(self.s1.name))
        self.assertFalse(self.fsm.stateExists(self.s2.name))
        self.fsm.addState(self.s2)
        self.assertTrue(self.fsm.stateExists(self.s2.name))

    def test_getStateByName(self):
        self.fsm.addState(self.s1)
        self.assertRaises(TypeError, self.fsm.getStateByName, 1)
        self.assertRaises(TypeError, self.fsm.getStateByName, self.s1)
        s1_found = self.fsm.getStateByName(self.s1.name)
        self.assertTrue(isinstance(s1_found, State))
        self.assertEqual('s1', s1_found.name)
        self.assertRaises(KeyError, self.fsm.getStateByName, 's2')

    def test_addTransition(self):
        self.fsm.addState(self.s1)
        self.assertRaises(TypeError, self.fsm.addTransition, self.s1)
        self.assertRaises(TypeError, self.fsm.addTransition, "a string")
        self.fsm.addTransition(self.t1)
        # Failed - no boolean return, runtime error?
        self.assertFalse(self.fsm.transitions)
        self.fsm.addState(self.s2)
        self.fsm.addTransition(self.t1)
        self.assertEqual(1, len(self.fsm.transitions))
        self.fsm.addTransition(self.t2)
        self.assertEqual(2, len(self.fsm.transitions))

    def test_deleteTransition(self):
        self.assertRaises(TypeError, self.fsm.deleteTransition, "garbage")
        self.fsm.addState(self.s1)
        self.fsm.addState(self.s2)
        self.fsm.addTransition(self.t1)
        self.fsm.addTransition(self.t2)
        self.assertEqual(2, len(self.fsm.transitions))
        self.fsm.deleteTransition(self.t1)
        self.assertEqual(1, len(self.fsm.transitions))
        self.fsm.deleteTransition(self.t2)
        self.assertFalse(self.fsm.transitions)

    def test_getTransitionByEvent(self):
        self.assertRaises(TypeError, self.fsm.getTransitionsByEvent, 1)
        self.assertRaises(TypeError, self.fsm.getTransitionsByEvent, self.t1)
        self.fsm.addState(self.s1)
        self.fsm.addState(self.s2)
        self.fsm.addTransition(self.t1)
        self.fsm.addTransition(self.t2)
        self.assertEqual(2, len(self.fsm.transitions))
        self.assertFalse(self.fsm.getTransitionsByEvent("nothing"))
        self.assertEqual(1, len(self.fsm.getTransitionsByEvent("SomeEvent")))
        t3 = Transition(self.s2, "SomeEvent", self.s1,
            guard="SomeOtherCondition")
        self.fsm.addTransition(t3)
        self.assertEqual(3, len(self.fsm.transitions))
        self.assertEqual(2, len(self.fsm.getTransitionsByEvent("SomeEvent")))
        self.assertEqual(1,
            len(self.fsm.getTransitionsByEvent("SomeOtherEvent")))

if __name__ == '__main__':
    unittest.main()
