"""
Types and operations for SMEDL expressions
"""

from enum import Enum
from smedl.parser.exceptions import TypeMismatch

class SmedlType(Enum):
    """Represents the valid data types for SMEDL state variables and params.

    Enum members are given 2-tuples: (SMEDL type string, C type string). The
    SMEDL type string becomes the value of the member. Thus, to create a
    SmedlType from its string, do something like this:
        
        SmedlType('int')
        SmedlType('pointer')
        
    The C type string can then be accessed using the c_type property:
        
        SmedlType('float').c_type   // Evaluates to 'double'"""
    def __new__(cls, smedl_type, c_type):
        """Create enum members using only the SMEDL type string as the value and
        assigning the C type string to the c_type property"""
        obj = object.__new__(cls)
        obj._value_ = smedl_type
        obj.c_type = c_type
        return obj

    def __str__(self):
        """Return the SMEDL type string"""
        return self.value

    INT = ('int', 'int')
    FLOAT = ('float', 'double')
    CHAR = ('char', 'char')
    STRING = ('string', 'char *')
    POINTER = ('pointer', 'void *')
    THREAD = ('thread', 'pthread_t')
    OPAQUE = ('opaque', 'SMEDLOpaque')

    def convertible_to(self, other):
        """Return True if this SmedlType can convert to the other SmedlType
        (e.g. in assignment, parameters, etc.) and False if not."""
        # All numeric types can convert between each other.
        if (self in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR] and
                other in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]):
            return True
        # All other types are only compatible with themselves.
        elif self is other:
            return True
        else:
            return False

    # Useful in Jinja templates
    def is_a(self, name):
        """Check if name matches the provided string"""
        return self.name == name

# Notes on type checking:
# Types in expressions may be any of the SmedlTypes above, "null" if the value
# is a null pointer (compatible with POINTER and OPAQUE), and None if the value
# is a helper call (unknown, no type checking is done)

# Notes on parentheses:
# The code that initialized instances of these classes is responsible for
# determining whether parentheses are necessary around a particular expression
# and calling the parenthesize() method.

class Expression(object):
    """A SMEDL expression"""
    def __init__(self, type_, expr_type):
        self._type = type_
        self._parens = False
        # Needed by Jinja
        self._expr_type = expr_type

    @property
    def type(self):
        return self._type

    @property
    def parens(self):
        return self._parens

    @property
    def expr_type(self):
        return self._expr_type

    def parenthesize(self):
        """In child classes that are not atoms, parenthesize the expression. But
        by default, ignore."""
        pass

    def unary_type_check(self, op):
        """Check that the expression type is compatible with the given unary
        operation ("+", "-", "!", or "~"). Return the resulting type if so,
        raise TypeMismatch if not"""
        if op in ["+", "-"] and self._type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR, None]:
            return self.type
        elif op == "~" and self._type in [SmedlType.INT, SmedlType.CHAR, None]:
            return self.type
        elif op == "!" and self._type in [
                SmedlType.INT, SmedlType.CHAR, SmedlType.POINTER, None]:
            return self._type
        else:
            raise TypeMismatch("Cannot use {} on expression of type {}".format(
                op, self._type))

    def _arithmetic_type_check(self, other):
        """Check that the type of this expression is compatible with the other
        for a binary arithmetic operation (+, -, *, %, /). This expression is
        the left operand and the "other" is the right operand. Return the
        resulting type, or raise TypeMismatch if not compatible."""
        # If one or both operands are float and all are numbers, return float
        if (self._type == SmedlType.FLOAT and other._type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]) or (
                other._type == SmedlType.FLOAT and self._type in [
                SmedlType.INT, SmedlType.CHAR]):
            return SmedlType.FLOAT
        # If one or both operands are None and the rest are numbers, return None
        elif (self._type is None and other._type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR, None]) or (
                other._type is None and self._type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]):
            return None
        # If one or both operands are int and all are int or char, return int
        elif (self._type == SmedlType.INT and other._type in [
                SmedlType.INT, SmedlType.CHAR]) or (
                other._type == SmedlType.INT and self._type == SmedlType.CHAR):
            return SmedlType.INT
        # If both operands are char, return char
        elif self._type == SmedlType.CHAR and other._type == SmedlType.CHAR:
            return SmedlType.CHAR
        # Otherwise, type mismatch
        else:
            raise TypeMismatch()

    def _bitwise_type_check(self, other):
        """Check that the type of this expression is compatible with the other
        for a binary bitwise operation (<<, >>, &, ^, |). This expression is
        the left operand and the "other" is the right operand. Return the
        resulting type, or raise TypeMismatch if not compatible."""
        # If one/both operands are None and the rest are int/char, return None
        if (self._type is None and other._type in [
                SmedlType.INT, SmedlType.CHAR, None]) or (
                other._type is None and self._type in [
                SmedlType.INT, SmedlType.CHAR]):
            return None
        # If one or both operands are int and all are int or char, return int
        elif (self._type == SmedlType.INT and other._type in [
                SmedlType.INT, SmedlType.CHAR]) or (
                other._type == SmedlType.INT and self._type == SmedlType.CHAR):
            return SmedlType.INT
        # If both operands are char, return char
        elif self._type == SmedlType.CHAR and other._type == SmedlType.CHAR:
            return SmedlType.CHAR
        # Otherwise, type mismatch
        else:
            raise TypeMismatch()

    def _comparison_type_check(self, other):
        """Check that the type of this expression is compatible with the other
        for a binary comparison or boolean operation (<, <=, >, >=, &&, ||).
        These are fundamentally different operations, however, their type
        requirements happen to be the same. This expression is
        the left operand and the "other" is the right operand. Return the
        resulting type, or raise TypeMismatch if not compatible."""
        # If both operands are numbers or None, return int
        if (self._type in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR, None]
                and other._type in [SmedlType.INT, SmedlType.FLOAT,
                SmedlType.CHAR, None]):
            return SmedlType.INT
        # Otherwise, type mismatch
        else:
            raise TypeMismatch()

    def _equality_type_check(self, other):
        """Check that the type of this expression is compatible with the other
        for a binary equality operation (==, !=). This expression is
        the left operand and the "other" is the right operand. Return the
        resulting type, or raise TypeMismatch if not compatible."""
        # If either operand is None, other operand can be anything. Return int
        if self._type is None or other._type is None:
            return SmedlType.INT
        # If both operands are numbers, return int
        elif (self._type in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]
                and other._type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]):
            return SmedlType.INT
        # If either operand is "null", the other can be "null" or pointer.
        # Return int
        elif (self._type == "null" and other._type in [
                SmedlType.POINTER, "null"]) or (
                other._type == "null" and self._type == SmedlType.POINTER):
            return SmedlType.INT
        # If both operands are the same type, return int
        elif self._type == other._type:
            return SmedlType.INT
        # Otherwise, type mismatch
        else:
            raise TypeMismatch()

    def binary_type_check(self, op, other):
        """Check that the expression type is compatible with the given binary
        operation. This expression is the left operand, the "other" parameter
        is the right operand. Return the resulting type if so, raise
        TypeMismatch if not"""
        try:
            if op in ['*', '/', '%', '+', '-']:
                return self._arithmetic_type_check(other)
            elif op in ['<<', '>>', '&', '^', '|']:
                return self._bitwise_type_check(other)
            elif op in ['<', '<=', '>', '>=', '&&', '||']:
                # Boolean operators are fundamentally different operators from
                # comparison operators, however, their type requirements happen
                # to be the same
                return self._comparison_type_check(other)
            elif op in ['==', '!=']:
                return self._equality_type_check(other)
            else:
                # Should not happen. Means the grammar allowed an operator that
                # the code above cannot handle.
                raise ValueError("Internal error: unknown operation {}".format(
                    op))
        except TypeMismatch as e:
            raise TypeMismatch("Cannot use {} on expressions of type {} and {}"
                    .format(op, self.type, other.type)) from e

    def assignment_type_check(self, dest_type):
        """Check that the expression type is compatible with the destination
        SmedlType. Useful for state variable assignments, type checking for
        event parameters, etc. If compatible, nothing happens. If not, raise
        TypeMismatch."""
        # None is compatible with all types
        if self._type is None:
            return
        # "null" is compatible with POINTER
        elif self._type == "null" and dest_type == SmedlType.POINTER:
            return
        # Otherwise, determine according to SmedlType.convertible_to()
        elif self._type.convertible_to(dest_type):
            return
        # If none of the other cases matched, we have a type mismatch
        else:
            raise TypeMismatch("{} cannot be used as a {}".format(self._type,
                dest_type))

class StateVar(Expression):
    """A state variable usage"""
    def __init__(self, name, type_):
        super().__init__(type_, 'state_var')
        """Initialize the StateVar.

        Parameters:
        name - Name of the state variable
        type_ - The SMEDL type of the state variable
        """
        self._name = name

    @property
    def name(self):
        return self._name

    def __repr__(self):
        return "StateVar:" + self._name

class EventParam(Expression):
    """An event parameter usage. Event parameters are referred to internally by
    their index in the parameter list, as the parameters can be given different
    names each time the event is used in a transition."""
    def __init__(self, idx, type_):
        """Initialize the EventParam.

        Parameters:
        idx - The index of the parameter in the param list.
        type_ - The SMEDL type of the parameter.
        """
        super().__init__(type_, 'param')
        self._idx = idx

    @property
    def idx(self):
        return self._idx

    def __repr__(self):
        return "EvParam:" + str(self._idx)

class Literal(Expression):
    """A literal in an expression"""
    def __init__(self, string, type_):
        """Initialize the literal.

        Parameters:
        string - The literal's representation in C syntax, e.g. "123" for an
          integer or "'a'" for a char
        type_ - The SMEDL type of the literal
        """
        super().__init__(type_, 'literal')
        self._string = string

    @property
    def string(self):
        return self._string

    def __repr__(self):
        return self._string

class HelperCall(Expression):
    """A call to a helper function in an expression"""
    def __init__(self, name, params):
        """Initialze the HelperCall.

        Parameters:
        name - The name of the helper function
        params - An iterable of Expressions to be passed as parameters to the
          helper function
        """
        super().__init__(None, 'helper_call')
        self._name = name
        self._params = tuple(params)

    @property
    def name(self):
        return self._name

    @property
    def params(self):
        return self._params

    def __repr__(self):
        return (self._name + '(' + ', '.join([repr(p) for p in self._params]) +
                ')')

class UnaryOp(Expression):
    """A unary operation in an expression"""
    def __init__(self, operator, operand):
        """Initialize the UnaryOp. Raise a TypeMismatch if the type is not
        compatible.

        Parameters:
        operator - The operator, as a string (e.g. "+", "-", "~", "!")
        operand - The operand, an expression type from this module
        """
        super().__init__(operand.unary_type_check(operator), 'unary_op')
        self._operator = operator
        self._operand = operand

    @property
    def operator(self):
        return self._operator

    @property
    def operand(self):
        return self._operand

    def parenthesize(self):
        self._parens = True

    def __repr__(self):
        if self._parens:
            return ''.join(['(', self._operator, ' ', repr(self._operand), ')'])
        else:
            return ''.join([self._operator, ' ', repr(self._operand)])

class BinaryOp(Expression):
    """A binary operation in an expression"""
    def __init__(self, operator, left, right):
        """Initialize the BinaryOp. Raise a TypeMismatch if the types are not
        compatible.

        Parameters:
        operator - The operator, as a string (e.g. "+", "/", ">>", "!=", etc.)
        left - The left operand, an expression from this module
        right - The right operand, an expression from this module
        """
        super().__init__(left.binary_type_check(operator, right), 'binary_op')
        self._operator = operator
        self._left = left
        self._right = right

    @property
    def operator(self):
        return self._operator

    @property
    def left(self):
        return self._left

    @property
    def right(self):
        return self._right

    def parenthesize(self):
        self._parens = True

    def __repr__(self):
        if self._parens:
            return ''.join(['(', repr(self._left), ' ', self._operator, ' ',
                    repr(self._right), ')'])
        else:
            return ''.join([repr(self._left), ' ', self._operator, ' ',
                repr(self._right)])
