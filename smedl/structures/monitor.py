"""
Structures and types for SMEDL monitors (.smedl files)
"""

from . import expr
from smedl.parser.exceptions import NameCollision, ElseCollision

class StateVariable(object):
    """Stores the information for a single state variable in a SMEDL spec"""
    def __init__(self, name, type_, initial_value=None):
        self.name = name
        self.type = type_ # SMEDL type
        if initial_value is not None:
            self.initial_value = initial_value
        else:
            if self.type == 'int':
                self.initial_value = "0"
            elif self.type == 'float':
                self.initial_value = "0.0"
            elif self.type == 'char':
                self.initial_value = "'\\0'"
            elif self.type == 'string':
                self.initial_value = '""'
            elif self.type == 'pointer':
                self.initial_value = "NULL"
            elif self.type == 'thread':
                self.initial_value = None
            elif self.type == 'opaque':
                #TODO This may cause errors converting a const char * to
                # non-const void * in C++. (C should not complain.)
                self.initial_value = '{"", 0}'

class Action(object):
    """A base class for all the action types that may appear in the list of
    actions for a transition step."""
    def __init__(self, action_type):
        """Initialize the action

        Parameters:
        action_type - A string describing the type of action for use with Jinja
        """
        self.action_type = action_type

class AssignmentAction(Action):
    """An action representing assigning an expression to a state variable"""
    def __init__(self, var, expr):
        """Initialize the assignment.

        Parameters:
        var - The name of the state variable to assign to
        expr - An expr.Expression to be assigned to it
        """
        super().__init__('assignment')
        self.var = var
        self.expr = expr

class IncrementAction(Action):
    """An action representing incrementing a state variable"""
    def __init__(self, var):
        """Initialize the increment using the provided state variable name."""
        super().__init__('increment')
        self.var = var

class DecrementAction(Action):
    """An action representing decrementing a state variable"""
    def __init__(self, var):
        """Initialize the decrement using the provided state variable name."""
        super().__init__('decrement')
        self.var = var

class RaiseAction(Action):
    """An action representing raising an event"""
    def __init__(self, event, params):
        """Initialize the raise action.

        Parameters:
        event - The name of the event to be raised
        params - Parameters of the event as a list of expr.Expression
        """
        super().__init__('raise')
        self.event = event
        self.params = params

class CallAction(Action):
    """An action representing a call to a helper function."""
    #TODO Using a helper on its own like this should be considered deprecated.
    # It is only useful if helpers have side effects, which is not supposed to
    # be allowed (but we do not currently enforce).
    def __init__(self, function, params):
        """Initialize the function call action.

        Parameters:
        function - The name of the helper function to call
        params - Parameters of the call as a list of expr.Expression
        """
        super().__init__('call')
        self.function = function
        self.params = params

class Scenario(object):
    """Stores the information for a single scenario in a SMEDL spec"""
    def __init__(self, name):
        self.name = name
        # List of state names: The first state in the list is the initial state
        self.states = []
        # Implicit states are created when a scenario has a transition that goes
        # directly into another transition, e.g.:
        # 
        #    state_a -> event1() -> event2() -> state_b
        #
        # This would create an implicit state between event1 and event2.
        # Implicit states are given numbers sequentially, so we need to keep
        # track of how many exist so far.
        #
        # In the generated code, implicit states get names like "_state0"
        self.implicit_states = 0
        # Steps: Single steps from a transition.
        # Keys are 2-tuples (state, event name) representing the state the step
        #   leads from and the event it is for. State is either a string if it
        #   is a named state or an integer if it is an implicit state.
        # Values are lists of 3-tuples (condition, dest state, list of actions)
        #   where condition is an Expression (that should evaluate to an INT,
        #   FLOAT, or CHAR), dest state is a string or int as above, and list of
        #   actions is precisely a list of Action.
        self.steps = dict()
        # Else transitions: Keys are 2-tuples (state, event name) and
        # values are 2-tuples (dest state, list of Actions)
        self.elses = dict()

    def _add_state(self, name):
        """Add a state to the scenario, if a string and not already present. The
        first state added becomes the initial state."""
        if isinstance(name, str) and name not in self.states:
            self.states.append(name)

    def get_implicit_state(self):
        """Get the next unused implicit state number"""
        state = self.implicit_states
        self.implicit_states += 1
        return state

    def all_states(self):
        """Get a list of all states, explicit and implicit"""
        return self.states + list(range(self.implicit_states))

    def _add_else(self, from_state, event, to_state, actions):
        """Add else actions to a particular state-event pair"""
        if to_state is not None:
            key = (from_state, event)
            if key in self.elses:
                raise ElseCollision("An else is already defined for {}/{}"
                        .format(from_state, event))
            self.elses[key] = (to_state, actions)

    def add_step(self, from_state, event, condition, to_state, actions,
            else_state = None, else_actions = None):
        """Add a step to the scenario

        Parameters:
        from_state - Name of state (or number of implicit state) this step is
          from. If state does not exist yet, it will be added. Note that the
          first from state of the first step added will become the starting
          state for the scenario!
        event - Name of event this step is for.
        condition - An Expression representing the condition for this step, or
          None if no condition
        to_state - Name of state (or number of implicit state) this step is to
        actions - A list of Action
        else_state - Name of the "else state" or None if not provided. This may
          only be provided for each from_state/event pair *once* or an
          ElseCollision is raised
        else_actions - A list of Action to occur when transitioning to the else
          state
        """

        # Add the from, to, and else states if necessary
        self._add_state(from_state)
        self._add_state(to_state)
        self._add_state(else_state)

        # If condition is None, convert to a true Expression (1)
        if condition is None:
            condition = expr.Literal('1', expr.SmedlType.INT)

        # Add a new entry to the steps dict
        key = (from_state, event)
        value = (condition, to_state, actions)
        try:
            self.steps[key].append(value)
        except KeyError:
            self.steps[key] = [value]
        
        # Add the else
        self.add_else(from_state, event, else_state, else_actions)

    def handles_event(self, event):
        """Check if this scenario has any transitions for the specified event.
        Return True or False.

        Parameters:
        event - The name of the event to check for
        """
        for key in self.steps.keys():
            if key[2] == event:
                return True
        return False

class MonitorSpec(object):
    """A monitor specification from a .smedl file"""
    def __init__(self, name):
        """Instantiate a new MonitorSpec to hold the data from a .smedl file"""
        # Name of the monitor.
        self.name = name
        # List of helper header files, with the enclosing "" or <>
        self.helpers = []
        # State vars: list of StateVariable
        self.state_vars = []
        # Imported, internal, and exported events: keys are names, values are
        # lists of SmedlType representing their parameters
        self.imported_events = dict()
        self.internal_events = dict()
        self.exported_events = dict()
        # List of Scenarios containing the state machines themselves
        self.scenarios = []

    def add_helper(self, helper):
        """Add a header file for helper functions. helper is a string containing
        the text to come after #include, e.g. '<helper.h>' or '"helper.h"'"""
        self.helpers.append(helper)

    def add_state_var(self, name, type_, initial_value=None):
        """Add a state variable to the monitor. If an initial value isn't
        provided, a default will be used."""
        self.state_vars.append(StateVariable(name, type_, initial_value))

    def add_event(self, type_, name, param_list):
        """Add an event to the monitor. The type must be a string that's either
        "imported", "internal", or "exported". The name is a string and the
        param_list is a list of SmedlType."""
        if (name in self.imported_events
                or name in self.internal_events
                or name in self.exported_events):
            raise NameCollision("Event {} already defined".format(name))

        if type_ == "imported":
            self.imported_events[name] = param_list
        elif type_ == "internal":
            self.internal_events[name] = param_list
        elif type_ == "exported":
            self.exported_events[name] = param_list
        else:
            raise ValueError("Unexpected event type {}".format(type_))

    def add_scenario(self, scenario):
        """Add a Scenario to the monitor. If a scenario with the same name is
        already present, raise NameCollision."""
        # Check for name collisions
        for s in self.scenarios:
            if s.name == scenario.name:
                raise NameCollision("A scenario with name {} already exists"
                        .format(scenario.name))
        self.scenarios.append(scenario)

    def get_event(self, name):
        """Retrieve the list of SmedlType representing an events parameters,
        whether it be an imported, internal, or exported event. Return None
        if the name is not a valid event."""
        if name in self.imported_events:
            return self.imported_events[name]
        elif name in self.internal_events:
            return self.internal_events[name]
        elif name in self.exported_events:
            return self.exported_events[name]
        else:
            return None

    def var_type(self, name):
        """Get the SmedlType of the named state variable"""
        for var in self.state_vars:
            if var.name == name:
                return var.type


    def __repr__(self):
        #TODO Proably do this by adding __repr__ to components and calling those
        pass
