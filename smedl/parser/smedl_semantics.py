"""
SMEDL file semantic actions
"""

from structures import monitor, expr
from . import common_semantics
from .exceptions import TypeMismatch, NameNotDefined

class SmedlSemantics(common_semantics.CommonSemantics):
    """Semantic actions for SMEDL parsing"""
    def start(self, ast):
        """Return the MonitorSpec object"""
        return self.monitor

    def declaration(self, ast):
        """Create the MonitorSpec object"""
        self.monitor = monitor.MonitorSpec(ast)
        return ast

    def helper_definition(self, ast):
        """Add a helper file"""
        self.monitor.add_helper(ast)
        return ast

    def _initial_value_matches(self, var_type, value_type):
        if var_type is expr.SmedlType.INT:
            return value_type in ['int', 'char']
        elif var_type is expr.SmedlType.FLOAT:
            return value_type in ['float', 'int']
        elif var_type is expr.SmedlType.CHAR:
            return value_type in ['char', 'int']
        elif var_type is expr.SmedlType.STRING:
            return value_type == 'string'
        elif var_type is expr.SmedlType.POINTER:
            return value_type == 'null'
        elif var_type is expr.SmedlType.THREAD:
            return False
        elif var_type is expr.SmedlType.OPAQUE:
            return value_type == 'null'

    def state_declaration(self, ast):
        """Add a state variable to the monitor"""
        var_name = ast.name
        var_type = ast.type
        value = ast.value

        # Check type of the initial value
        if (value is not None and
                not self._inital_value_matches(var_type, value.type)):
            raise TypeMismatch(
                    "State var {} initialized to incompatible value {}.".format(
                        var_name, value.value))
        
        # Add to the monitor
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
            if transition.else_definition is not None:
                else_state = transition.else_definition.else_state
                else_actions = transition.else_definition.else_actions
            else:
                else_state = None
                else_actions = None

            # Loop over the steps in the transition and add to the scenario
            from_state = transition.start_state
            for step in transition.steps[:-1]:
                # All steps except the last one go to an implicit state
                to_state = scenario.get_implicit_state()
                event_name = step.event.name
                condition = step.condition
                actions = step.action_list
                scenario.add_step(from_state, event_name, condition, to_state,
                        actions, else_state, else_actions)
                from_state = to_state
            # Do the last iteration separately - to_state = transition.end_state
            step = transition.steps[-1]
            to_state = transition.end_state
            event_name = step.event.name
            condition = step.condition
            actions = step.action_list
            scenario.add_step(from_state, event_name, condition, to_state,
                    actions, else_state, else_actions)
        
        # Add the scenario to the monitor
        self.monitor.add_scenario(scenario)
        return ast

    def step_definition_list(self, ast):
        """Store whether there is a single or multiple steps in this transition.
        else_preproc will need this to determine whether to allow else actions
        to use event parameter bindings."""
        if len(ast) > 1:
            self.multiple_steps = True
        else:
            self.multiple_steps = False
        return ast

    def step_definition(self, ast):
        """Step definitions may not have actions, in which case the actions
        key will store None. In that case, convert it to an empty list."""
        if ast.actions is None:
            ast.actions = []
        return ast

    def else_definition(self, ast):
        """Else definitions may not have actions, in which case the actions
        key will store None. In that case, convert it to an empty list."""
        if ast.else_actions is None:
            ast.else_actions = []
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
        self.current_event_params = ast.params # Will be a list of names as strs

        # Verify that event exists, is an imported or internal event, and that
        # the parameter count matches
        if ast.name in self.monitor.imported_events:
            if len(self.monitor.imported_events[ast.name]) != len(ast.params):
                raise NameNotDefined("{} event has incorrect number of "
                        "parameters".format(ast.name))
        elif ast.name in self.monitor.internal_events:
            if len(self.monitor.internal_events[ast.name]) != len(ast.params):
                raise NameNotDefined("{} event has incorrect number of "
                        "parameters".format(ast.name))
        else:
            raise NameNotDefined("{} event is not an imported or internal "
                    "event.".format(ast.name))

        return ast

    ### Expression type checking ##############################################

    # Note: All type_ parameters should be either a SmedlType, "null", or None.
    # None if it is a helper function or an expression with a helper function
    # (as we cannot type check these); "null" if it is a null pointer (valid
    # for either POINTER or OPAQUE types; SmedlType otherwise.

    def atom(self, ast):
        """Convert the atom to the proper Expression type with type info"""
        if ast.type is not None:
            # Literal
            if ast.type in ["int", "char"]
                # C treats both of these as int literals
                return expr.Literal(ast.value, expr.SmedlType.INT)
            elif ast.type == "float":
                return expr.Literal(ast.value, expr.SmedlType.DOUBLE)
            elif ast.type == "string":
                return expr.Literal(ast.value, expr.SmedlType.STRING)
            elif ast.type == "null":
                return expr.Literal(ast.value, "null")

        elif isinstance(ast, str):
            # State variable or event parameter
            try:
                param_idx = self.current_event_params.index(ast)
                if self.current_event in self.monitor.imported_events:
                    param_type = self.monitor.imported_events[
                            self.current_event]
                elif self.current_event in self.monitor.internal_events:
                    param_type = self.monitor.internal_events[
                            self.current_event]
                return expr.EventParam(param_idx, param_type)
            except ValueError:
                # Not an event parameter. Must be a state variable.
                try:
                    state_var = self.monitor.state_vars[ast]
                    type_ = state_var.type
                    return expr.StateVar(ast, type_)
                except KeyError:
                    raise NameNotDefined("Variable {} is not an event parameter"
                            " or state variable.".format(ast))

        elif ast[0] == '(':
            # Parenthesized expression
            ast[1].parenthesize()
            return ast[1]

        else:
            # Helper function call
            return expr.HelperCall(ast[0], ast[2])

    def unary_expr(self, ast):
        """Type check the unary_expr and create a UnaryOp"""
        if isinstance(ast, Expression):
            return ast
        elif ast[0] in ["+", "-"] and ast[1].type in [
                expr.SmedlType.INT,
                expr.SmedlType.FLOAT,
                expr.SmedlType.CHAR]:
            return expr.UnaryOp(ast[0], ast[1], ast[1].type)
        elif ast[0] in ["~", "!"] and ast[1].type in [
                expr.SmedlType.INT,
                expr.SmedlType.CHAR]:
            return expr.UnaryOp(ast[0], ast[1], ast[1].type)
        elif ast[1].type is None:
            return expr.UnaryOp(ast[0], ast[1], ast[1].type)
        else:
            raise TypeMismatch("Cannot use {} on expression of type {}".format(
                ast[0], ast[1].type))

    def expression(self, ast):
        """Type check all binary expressions and create BinaryOps from them"""
        # This will receive a "tree" of 3-tuples where first element is the
        # operator, second is the left operand, and third is the right operand.
        # This must be processed recursively.
        if isinstance(ast, Expression):
            return ast
        
        left = self.expression(ast[1])
        right = self.expression(ast[2])

        # Type check arithmetic operators
        if ast[0] in ['*', '/', '%', '+', '-']:
            # If one or both operands are float and all are numbers, type=float
            if (left.type == expr.SmedlType.FLOAT and right.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.FLOAT,
                        expr.SmedlType.CHAR]) or (
                    right.type == expr.SmedlType.FLOAT and left.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.CHAR]):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.FLOAT)
            # If one or both operands are None and rest are numbers, type=None
            elif (left.type is None and right.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.FLOAT,
                        expr.SmedlType.CHAR,
                        None]) or (right.type is None and left.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.FLOAT,
                        expr.SmedlType.CHAR]):
                return expr.BinaryOp(ast[0], ast[1], ast[2], None)
            #If one or both operands are int and all are int or char, type=int
            elif (left.type == expr.SmedlType.INT and right.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.CHAR]) or (
                    right.type == expr.SmedlType.INT and
                    left.type == expr.SmedlType.CHAR):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.INT)
            #If both operands are char, type=char
            elif (left.type == expr.SmedlType.CHAR and
                    right.type == expr.SmedlType.CHAR):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.CHAR)
            else:
                raise TypeMismatch("Cannot use {} on expressions of type {} "
                    "and {}".format(ast[0], ast[1].type, ast[2].type))

        # Type check bitwise operators
        elif ast[0] in ['<<', '>>', '&', '^', '|']:
            # If one or both operands are None and rest are int/char, type=None
            elif (left.type is None and right.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.CHAR,
                        None]) or (right.type is None and left.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.CHAR]):
                return expr.BinaryOp(ast[0], ast[1], ast[2], None)
            #If one or both operands are int and all are int or char, type=int
            elif (left.type == expr.SmedlType.INT and right.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.CHAR]) or (
                    right.type == expr.SmedlType.INT and
                    left.type == expr.SmedlType.CHAR):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.INT)
            #If both operands are char, type=char
            elif (left.type == expr.SmedlType.CHAR and
                    right.type == expr.SmedlType.CHAR):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.CHAR)
            else:
                raise TypeMismatch("Cannot use {} on expressions of type {} "
                    "and {}".format(ast[0], ast[1].type, ast[2].type))

        # Type check comparison operators and boolean operators (while they are
        # fundamentally different operations, their type requirements happen to
        # be the same)
        elif ast[0] in ['<', '<=', '>', '>=', '&&', '||']:
            # If both operands are numbers or None, type=int
            if (left.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.FLOAT,
                        expr.SmedlType.CHAR,
                        None]
                    and right.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.FLOAT,
                        expr.SmedlType.CHAR,
                        None]):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.INT)
            else:
                raise TypeMismatch("Cannot use {} on expressions of type {} "
                    "and {}".format(ast[0], ast[1].type, ast[2].type))

        # Type check equality operators
        elif ast[0] in ['==', '!=']:
            # If either operand is None, other operand can be anything, type=int
            if left.type is None or right.type is None:
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.INT)
            # If both operands are numbers, type=int
            elif (left.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.FLOAT,
                        expr.SmedlType.CHAR]
                    and right.type in [
                        expr.SmedlType.INT,
                        expr.SmedlType.FLOAT,
                        expr.SmedlType.CHAR]):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.INT)
            # If either operand is "null", the other can be "null", pointer, or
            # opaque. type=int
            elif (left.type == "null" and right.type in [
                    expr.SmedlType.POINTER,
                    expr.SmedlType.OPAQUE,
                    "null"]) or (right.type == "null" and left.type in [
                    expr.SmedlType.POINTER,
                    expr.SmedlType.OPAQUE]):
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.INT)
            # If both operands are the same type, type=int
            elif left.type == right.type:
                return expr.BinaryOp(ast[0], ast[1], ast[2],
                        expr.SmedlType.INT)
            else:
                raise TypeMismatch("Cannot use {} on expressions of type {} "
                    "and {}".format(ast[0], ast[1].type, ast[2].type))

        # This should not happen. It means the code above missed an operator.
        else:
            raise ValueError("Internal error: unknown operation {}"
                    .format(ast[0]))

    ###########################################################################

    def signed_literal(self, ast):
        """Signed literals are only used for state initialization. Join the
        signed variants into single strings."""
        if ast.type == 'signed_int':
            ast.type = 'int'
            ast.value = ''.join(ast.value)
        elif ast.type == 'signed_float':
            ast.type = 'float'
            ast.value = ''.join(ast.value)
        return ast
