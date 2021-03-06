# Copyright (c) 2021 The Trustees of the University of Pennsylvania
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""
SMEDL file semantic actions
"""

from smedl.structures import monitor, expr
from . import common_semantics
from .exceptions import TypeMismatch, NameNotDefined


class SmedlSemantics(common_semantics.CommonSemantics):
    """Semantic actions for SMEDL parsing"""
    def __init__(self, path):
        """Do some basic initialization

        path - The directory the .smedl file resides in"""
        self.path = path
        # self.monitor is created in declaration()

    def start(self, ast):
        """Return the MonitorSpec object"""
        return self.monitor

    def declaration(self, ast):
        """Create the MonitorSpec object"""
        self.monitor = monitor.MonitorSpec(ast, self.path)
        return ast

    def helper_definition(self, ast):
        """Add a helper file"""
        self.monitor.add_helper(ast)
        return ast

    def _initial_value_matches(self, var_type, value_type):
        if var_type is expr.SmedlType.INT:
            # Float is normally permitted for assignment to int, but if used
            # for initialization, something is likely wrong.
            return value_type in ['int', 'char']
        elif var_type is expr.SmedlType.FLOAT:
            return value_type in ['float', 'int', 'char']
        elif var_type is expr.SmedlType.CHAR:
            return value_type in ['char', 'int']
        elif var_type is expr.SmedlType.STRING:
            return value_type == 'string'
        elif var_type is expr.SmedlType.POINTER:
            return value_type == 'null'
        elif var_type is expr.SmedlType.OPAQUE:
            # TODO Should we allow opaques to be initialized like strings?
            return False

    def state_declaration(self, ast):
        """Add a state variable to the monitor"""
        var_name = ast.name
        var_type = ast.type
        value = ast.value

        # Check type of the initial value
        if (value is not None and
                not self._initial_value_matches(var_type, value.type)):
            raise TypeMismatch(
                "State var {} initialized to incompatible value {}.".format(
                    var_name, value.value))

        # Add to the monitor (and check if already declared)
        if value is None:
            self.monitor.add_state_var(var_name, var_type)
        else:
            self.monitor.add_state_var(var_name, var_type, value.value)

        return ast

    def event_declaration(self, ast):
        """Add events from an event declaration to the monitor"""
        ev_type = ast.type

        # One declaration can declare multiple events
        for signature in ast.signatures:
            ev_name = signature.name
            ev_params = signature.params
            self.monitor.add_event(ev_type, ev_name, ev_params)

        return ast

    def scenario(self, ast):
        """Add a scenario to the monitor"""
        # Create an empty scenario
        scenario = monitor.Scenario(ast.name)

        # Populate the states and transitions of the scenario
        for transition in ast.transitions:
            # Get else state and actions
            if transition.else_step is not None:
                else_state = transition.else_step.else_state
                else_actions = transition.else_step.else_actions
            else:
                else_state = None
                else_actions = None

            # Loop over the steps in the transition and add to the scenario
            from_state = transition.start_state
            for step in transition.steps.step_list[:-1]:
                # All steps except the last one go to an implicit state
                to_state = scenario.get_implicit_state()
                event_name = step.event.name
                condition = step.condition
                actions = step.actions
                scenario.add_step(
                    from_state, event_name, condition, to_state, actions,
                    else_state, else_actions)
                from_state = to_state
            # Do the last iteration separately -
            #   to_state = transition.end_state
            step = transition.steps.step_list[-1]
            to_state = transition.steps.end_state
            event_name = step.event.name
            condition = step.condition
            actions = step.actions
            scenario.add_step(
                from_state, event_name, condition, to_state, actions,
                else_state, else_actions)

        # If a final state was given, check if it exists and add it
        if ast.final_state is not None:
            scenario.add_final_state(ast.final_state)

        # Add the scenario to the monitor
        self.monitor.add_scenario(scenario)
        return ast

    def step_definition_list(self, ast):
        """Transform the AST into a list of steps (ast.step_list) and an end
        state (ast.end_state). Also store whether there is a single or multiple
        steps in the transition, as else_preproc will need this to determine
        whether to allow else actions to use event parameter bindings."""
        step_list = [ast.step]
        if ast.rest is None:
            self.multiple_steps = False
        else:
            self.multiple_steps = True
            step_list.extend(ast.rest.step_list)
            ast['end_state'] = ast.rest.end_state
            del ast['rest']
        del ast['step']
        ast['step_list'] = step_list
        return ast

    def step_definition(self, ast):
        """Step definitions may not have actions, in which case the actions
        key will store None. In that case, convert it to an empty list."""
        if ast.actions is None:
            ast['actions'] = []
        return ast

    def else_definition(self, ast):
        """Else definitions may not have actions, in which case the actions
        key will store None. In that case, convert it to an empty list."""
        if ast.else_actions is None:
            ast['else_actions'] = []
        return ast

    def else_preproc(self, ast):
        """If there are multiple steps in this transition, clear the event
        parameter bindings before processing the else actions."""
        if self.multiple_steps:
            self.current_event = None
            self.current_event_params = []
        return ast

    def step_event_definition(self, ast):
        """Store the parameter name bindings for the current event so they are
        available to actions and conditions in this step."""
        self.current_event = ast.name
        self.current_event_params = ast.params  # Will be a list of (str) names

        # Verify that event exists and that the parameter count matches
        if ast.name in self.monitor.imported_events:
            if len(self.monitor.imported_events[ast.name]) != len(ast.params):
                raise NameNotDefined("{} event has incorrect number of "
                                     "parameters".format(ast.name))
        elif ast.name in self.monitor.internal_events:
            if len(self.monitor.internal_events[ast.name]) != len(ast.params):
                raise NameNotDefined("{} event has incorrect number of "
                                     "parameters".format(ast.name))
        elif ast.name in self.monitor.exported_events:
            if len(self.monitor.exported_events[ast.name]) != len(ast.params):
                raise NameNotDefined("{} event has incorrect number of "
                                     "parameters".format(ast.name))
        else:
            raise NameNotDefined("{} event is not an imported, internal, or"
                                 "exported event.".format(ast.name))

        return ast

    def action_inner_list(self, ast):
        """Convert action_inner_lists into an actual list"""
        if ast.first is None:
            result = []
        else:
            result = [ast.first]
        if ast.rest is not None:
            result.extend(ast.rest)
        return result

    def assignment(self, ast):
        """Verify that the state variable exists and the type matches the
        expression, then create the AssignmentAction"""
        # Verify that the state variable exists
        try:
            state_var = self.monitor.state_vars[ast.target]
        except KeyError:
            raise NameNotDefined("{} is not a state variable".format(
                ast.target))

        # Check type
        try:
            ast.value.assignment_type_check(state_var.type)
        except TypeMismatch:
            raise TypeMismatch(
                "Expression of type {} cannot be assigned to state variable "
                "{} of incompatible type {}".format(
                    ast.value.type, ast.target, state_var.type))

        # Create AssignmentAction
        return monitor.AssignmentAction(ast.target, ast.value)

    def increment(self, ast):
        """Verify that the state variable exists and is numeric or pointer, then
        create the IncrementAction"""
        # Verify that the state variable exists
        try:
            state_var = self.monitor.state_vars[ast.target]
        except KeyError:
            raise NameNotDefined("{} is not a state variable".format(
                ast.target))

        # Check type
        if state_var.type not in [
                expr.SmedlType.INT,
                expr.SmedlType.FLOAT,
                expr.SmedlType.CHAR,
                # TODO Allow pointer increment and decrement? If so, should we
                # also allow +/- on pointers?
                expr.SmedlType.POINTER]:
            raise TypeMismatch(
                "Cannot increment state variable {} of type {}"
                .format(ast.target, state_var.type))

        # Create action
        return monitor.IncrementAction(ast.target)

    def decrement(self, ast):
        """Verify that the state variable exists and is numeric or pointer, then
        create the DecrementAction"""
        # Verify that the state variable exists
        try:
            state_var = self.monitor.state_vars[ast.target]
        except KeyError:
            raise NameNotDefined("{} is not a state variable".format(
                ast.target))

        # Check type
        if state_var.type not in [
                expr.SmedlType.INT,
                expr.SmedlType.FLOAT,
                expr.SmedlType.CHAR,
                # TODO Allow pointer increment and decrement? If so, should we
                # also allow +/- on pointers?
                expr.SmedlType.POINTER]:
            raise TypeMismatch(
                "Cannot decrement state variable {} of type {}"
                .format(ast.target, state_var.type))

        # Create action
        return monitor.DecrementAction(ast.target)

    def raise_stmt(self, ast):
        """Verify that the event is an internal or exported event and do type
        checking on the parameters, then create the RaiseAction"""
        # Check that the event is internal or exported and the parameter count
        # matches
        if ast.event in self.monitor.exported_events:
            if len(self.monitor.exported_events[ast.event]) != len(ast.params):
                raise NameNotDefined("{} event has incorrect number of "
                                     "parameters".format(ast.event))
            else:
                event_params = self.monitor.exported_events[ast.event]
        elif ast.event in self.monitor.internal_events:
            if len(self.monitor.internal_events[ast.event]) != len(ast.params):
                raise NameNotDefined("{} event has incorrect number of "
                                     "parameters".format(ast.event))
            else:
                event_params = self.monitor.internal_events[ast.event]
        else:
            raise NameNotDefined("{} event is not an exported or internal "
                                 "event.".format(ast.event))

        # Type check the parameters
        for i in range(len(ast.params)):
            ast.params[i].assignment_type_check(event_params[i])

        # Create the RaiseAction
        return monitor.RaiseAction(ast.event, ast.params)

    def call_stmt(self, ast):
        """Create the CallAction"""
        # Calling a helper function as an action should be discouraged and
        # potentially depecated. Its only use would be functions with side
        # effects.
        # There is little verification we can do besides the type checking
        # already done by Expressions, so simply create the action.
        return monitor.CallAction(ast.function, ast.params)

    # Expressions and type checking ###########################################

    # Note: All type_ parameters should be either a SmedlType, "null", or None.
    # None if it is a helper function or an expression with a helper function
    # (as we cannot type check these); "null" if it is a null pointer (valid
    # for either POINTER or OPAQUE types; SmedlType otherwise.

    def literal(self, ast):
        """Convert a literal to an expr.Literal"""
        if ast.type in ["int", "char"]:
            # C treats both of these as int literals
            return expr.Literal(ast.value, expr.SmedlType.INT)
        elif ast.type == "float":
            return expr.Literal(ast.value, expr.SmedlType.FLOAT)
        elif ast.type == "string":
            return expr.Literal(ast.value, expr.SmedlType.STRING)
        elif ast.type == "null":
            return expr.Literal(ast.value, "null")

    def helper_call(self, ast):
        """Convert a helper function call to an expr.HelperCall"""
        return expr.HelperCall(ast.function, ast.params)

    def var_or_param(self, ast):
        """Convert a state variable or event parameter to an expr.StateVar or
        expr.EventParam"""
        try:
            param_idx = self.current_event_params.index(ast)
            if self.current_event in self.monitor.imported_events:
                param_type = self.monitor.imported_events[
                    self.current_event][param_idx]
            elif self.current_event in self.monitor.internal_events:
                param_type = self.monitor.internal_events[
                    self.current_event][param_idx]
            return expr.EventParam(param_idx, param_type)
        except ValueError:
            # Not an event parameter. Must be a state variable.
            try:
                state_var = self.monitor.state_vars[ast]
                type_ = state_var.type
                return expr.StateVar(ast, type_)
            except KeyError:
                raise NameNotDefined("Variable {} is not an event parameter "
                                     "or state variable.".format(ast))

    def parenthesized(self, ast):
        """Parenthesize an expression"""
        ast.parenthesize()
        return ast

    def unary_expr(self, ast):
        """Type check the unary_expr and create a UnaryOp"""
        if isinstance(ast, expr.Expression):
            return ast
        # This also does type checking
        return expr.UnaryOp(ast[0], ast[1])

    def expression(self, ast):
        """Type check all binary expressions and create BinaryOps from them"""
        # This will receive a "tree" of 3-tuples where first element is the
        # operator, second is the left operand, and third is the right operand.
        # This must be processed recursively.
        if isinstance(ast, expr.Expression):
            return ast

        left = self.expression(ast[1])
        right = self.expression(ast[2])

        # This also does type checking
        return expr.BinaryOp(ast[0], left, right)

    ###########################################################################

    def signed_literal(self, ast):
        """Signed literals are only used for state initialization. Join the
        signed variants into single strings."""
        if ast.type == 'signed_int':
            val = ast.value
            del ast['type']
            del ast['value']
            ast['type'] = 'int'
            ast['value'] = ''.join(val)
        elif ast.type == 'signed_float':
            val = ast.value
            del ast['type']
            del ast['value']
            ast['type'] = 'float'
            ast['value'] = ''.join(val)
        return ast
