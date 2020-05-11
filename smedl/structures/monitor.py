"""
Structures and types for SMEDL monitors (.smedl files)
"""

import types
from . import expr
from smedl.parser.exceptions import NameCollision, ElseCollision

class StateVariable(object):
    """Stores the information for a single state variable in a SMEDL spec"""
    def __init__(self, name, type_, initial_value=None):
        self._name = name
        self._type = type_ # SMEDL type
        if initial_value is not None:
            self._initial_value = initial_value
        else:
            if self._type == expr.SmedlType.INT:
                self._initial_value = "0"
            elif self._type == expr.SmedlType.FLOAT:
                self._initial_value = "0.0"
            elif self._type == expr.SmedlType.CHAR:
                self._initial_value = "'\\0'"
            elif self._type == expr.SmedlType.STRING:
                self._initial_value = '""'
            elif self._type == expr.SmedlType.POINTER:
                self._initial_value = "NULL"
            elif self._type == expr.SmedlType.THREAD:
                self._initial_value = None
            elif self._type == expr.SmedlType.OPAQUE:
                #TODO This may cause errors converting a const char * to
                # non-const void * in C++. (C should not complain.)
                self.initial_value = '{"", 0}'

    @property
    def name(self):
        return self._name

    @property
    def type(self):
        return self._type

    @property
    def initial_value(self):
        return self._initial_value

class Action(object):
    """A base class for all the action types that may appear in the list of
    actions for a transition step."""
    def __init__(self, action_type):
        """Initialize the action

        Parameters:
        action_type - A string describing the type of action for use with Jinja
        """
        self._action_type = action_type

    @property
    def action_type(self):
        return self._action_type

class AssignmentAction(Action):
    """An action representing assigning an expression to a state variable"""
    def __init__(self, var, expr):
        """Initialize the assignment.

        Parameters:
        var - The name of the state variable to assign to
        expr - An expr.Expression to be assigned to it
        """
        super().__init__('assignment')
        self._var = var
        self._expr = expr

    @property
    def var(self):
        return self._var

    @property
    def expr(self):
        return self._expr

class IncrementAction(Action):
    """An action representing incrementing a state variable"""
    def __init__(self, var):
        """Initialize the increment using the provided state variable name."""
        super().__init__('increment')
        self._var = var

    @property
    def var(self):
        return self._var

class DecrementAction(Action):
    """An action representing decrementing a state variable"""
    def __init__(self, var):
        """Initialize the decrement using the provided state variable name."""
        super().__init__('decrement')
        self._var = var

    @property
    def var(self):
        return self._var

class RaiseAction(Action):
    """An action representing raising an event"""
    def __init__(self, event, params):
        """Initialize the raise action.

        Parameters:
        event - The name of the event to be raised
        params - Parameters of the event as an iterable of expr.Expression
        """
        super().__init__('raise')
        self._event = event
        self._params = tuple(params)

    @property
    def event(self):
        return self._event

    @property
    def params(self):
        return self._params

class CallAction(Action):
    """An action representing a call to a helper function."""
    def __init__(self, function, params):
        """Initialize the function call action.

        Parameters:
        function - The name of the helper function to call
        params - Parameters of the call as an iterable of expr.Expression
        """
        super().__init__('call')
        self._function = function
        self._params = tuple(params)

    @property
    def function(self):
        return self._function

    @property
    def params(self):
        return self._params

class Scenario(object):
    """Stores the information for a single scenario in a SMEDL spec"""
    def __init__(self, name):
        self._name = name
        # List of state names: The first state in the list is the initial state
        self._states = []
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
        self._implicit_states = 0
        # Steps: Single steps from a transition.
        # Keys are 2-tuples (state, event name) representing the state the step
        #   leads from and the event it is for. State is either a string if it
        #   is a named state or an integer if it is an implicit state.
        # Values are lists of 3-tuples (condition, dest state, list of actions)
        #   where condition is an Expression (that should evaluate to an INT,
        #   FLOAT, or CHAR), dest state is a string or int as above, and list of
        #   actions is precisely a list of Action.
        self._steps = dict()
        # Else transitions: Keys are 2-tuples (state, event name) and
        # values are 2-tuples (dest state, list of Actions)
        self._elses = dict()

    @property
    def name(self):
        return self._name

    @property
    def states(self):
        return self._states

    @property
    def implicit_states(self):
        return self._implicit_states

    @property
    def all_states(self):
        """Get a list of all states, explicit and implicit"""
        return self.states + list(range(self.implicit_states))

    @property
    def steps(self):
        return types.MappingProxyType(self._steps)

    @property
    def elses(self):
        return types.MappingProxyType(self._elses)

    def get_implicit_state(self):
        """Get the next unused implicit state number"""
        state = self._implicit_states
        self._implicit_states += 1
        return state

    def _add_state(self, name):
        """Add a state to the scenario, if a string and not already present. The
        first state added becomes the initial state."""
        if isinstance(name, str) and name not in self._states:
            self._states.append(name)

    def _add_else(self, from_state, event, to_state, actions):
        """Add else actions to a particular state-event pair"""
        if to_state is not None:
            key = (from_state, event)
            if key in self._elses:
                raise ElseCollision("An else is already defined for {}/{}"
                        .format(from_state, event))
            self._elses[key] = (to_state, actions)

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
            self._steps[key].append(value)
        except KeyError:
            self._steps[key] = [value]
        
        # Add the else
        self._add_else(from_state, event, else_state, else_actions)

    def handles_event(self, event):
        """Check if this scenario has any transitions for the specified event.
        Return True or False.

        Parameters:
        event - The name of the event to check for
        """
        for key in self._steps.keys():
            if key[1] == event:
                return True
        return False

class MonitorSpec(object):
    """A monitor specification from a .smedl file"""
    def __init__(self, name):
        """Instantiate a new MonitorSpec to hold the data from a .smedl file"""
        # Name of the monitor.
        self._name = name
        # List of helper header files, with the enclosing "" or <>
        self._helpers = []
        # State vars: keys are names, values are StateVariables
        self._state_vars = dict()
        ## State vars: list of StateVariable
        #self.state_vars = []
        # Imported, internal, and exported events: keys are names, values are
        # lists of SmedlType representing their parameters
        self._imported_events = dict()
        self._internal_events = dict()
        self._exported_events = dict()
        # List of Scenarios containing the state machines themselves
        self._scenarios = []

    @property
    def name(self):
        return self._name

    @property
    def helpers(self):
        return self._helpers

    @property
    def state_vars(self):
        return types.MappingProxyType(self._state_vars)

    @property
    def imported_events(self):
        return types.MappingProxyType(self._imported_events)

    @property
    def internal_events(self):
        return types.MappingProxyType(self._internal_events)

    @property
    def exported_events(self):
        return types.MappingProxyType(self._exported_events)

    @property
    def scenarios(self):
        return self._scenarios

    def add_helper(self, helper):
        """Add a header file for helper functions. helper is a string containing
        the text to come after #include, e.g. '<helper.h>' or '"helper.h"'"""
        self._helpers.append(helper)

    def add_state_var(self, name, type_, initial_value=None):
        """Add a state variable to the monitor after checking for duplicate
        declaration. If an initial value isn't provided, a default will be used.
        """
        if name in self._state_vars:
            raise NameCollision("State variable {} already defined".format(
                var_name))
        self._state_vars[name] = StateVariable(name, type_, initial_value)

    def add_event(self, type_, name, param_list):
        """Add an event to the monitor. The type must be a string that's either
        "imported", "internal", or "exported". The name is a string and the
        param_list is an iterable of SmedlType."""
        if (name in self._imported_events
                or name in self._internal_events
                or name in self._exported_events):
            raise NameCollision("Event {} already defined".format(name))

        if type_ == "imported":
            self._imported_events[name] = tuple(param_list)
        elif type_ == "internal":
            self._internal_events[name] = tuple(param_list)
        elif type_ == "exported":
            self._exported_events[name] = tuple(param_list)
        else:
            raise ValueError("Unexpected event type {}".format(type_))

    def add_scenario(self, scenario):
        """Add a Scenario to the monitor. If a scenario with the same name is
        already present, raise NameCollision."""
        # Check for name collisions
        for s in self._scenarios:
            if s.name == scenario.name:
                raise NameCollision("A scenario with name {} already exists"
                        .format(scenario.name))
        self.scenarios.append(scenario)

    def get_event(self, name):
        """Retrieve the list of SmedlType representing an events parameters,
        whether it be an imported, internal, or exported event. Return None
        if the name is not a valid event."""
        if name in self._imported_events:
            return self._imported_events[name]
        elif name in self._internal_events:
            return self._internal_events[name]
        elif name in self._exported_events:
            return self._exported_events[name]
        else:
            return None

    def needs_handler(self, event):
        """Return True if any scenario handles the given event, False
        otherwise."""
        for s in self._scenarios:
            if s.handles_event(event):
                return True
        return False

    def __repr__(self):
        #TODO Proably do this by adding __repr__ to components and calling those
        pass
