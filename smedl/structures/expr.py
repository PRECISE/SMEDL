"""
Types and operations for SMEDL expressions
"""

from enum import Enum
from parser.exceptions import TypeMismatch

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

    def __str__(self):
        """Return the SMEDL type string"""
        return self.value

    INT = ('int', 'int')
    FLOAT = ('float', 'double')
    CHAR = ('char', 'char')
    STRING = ('string', 'char *')
    POINTER = ('pointer', 'void *')
    THREAD = ('thread', 'pthread_t')
    OPAQUE = ('opaque', 'void *')

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
    def __init__(self, type_):
        self.type = type_
        self.parens = False

    def parenthesize(self):
        """In child classes that are not atoms, parenthesize the expression. But
        by default, ignore."""
        pass

    def unary_type_check(self, op):
        """Check that the expression type is compatible with the given unary
        operation ("+", "-", "!", or "~"). Return the resulting type if so,
        raise TypeMismatch if not"""
        if op in ["+", "-"] and self.type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR, None]:
            return self.type
        elif op in ["~", "!"] and self.type in [
                SmedlType.INT, SmedlType.CHAR]:
            return self.type
        else:
            raise TypeMismatch("Cannot use {} on expression of type {}".format(
                op, self.type))

    def _arithmetic_type_check(self, other):
        """Check that the type of this expression is compatible with the other
        for a binary arithmetic operation (+, -, *, %, /). This expression is
        the left operand and the "other" is the right operand. Return the
        resulting type, or raise TypeMismatch if not compatible."""
        # If one or both operands are float and all are numbers, return float
        if (self.type == SmedlType.FLOAT and other.type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]) or (
                other.type == SmedlType.FLOAT and self.type in [
                SmedlType.INT, SmedlType.CHAR]):
            return SmedlType.FLOAT
        # If one or both operands are None and the rest are numbers, return None
        elif (self.type is None and other.type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR, None]) or (
                other.type is None and self.type in [
                SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]):
            return None
        # If one or both operands are int and all are int or char, return int
        elif (self.type == SmedlType.INT and other.type in [
                SmedlType.INT, SmedlType.CHAR]) or (
                other.type == SmedlType.INT and self.type == SmedlType.CHAR):
            return SmedlType.INT
        # If both operands are char, return char
        elif self.type == SmedlType.CHAR and other.type == SmedlType.CHAR:
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
        elif (self.type is None and other.type in [
                SmedlType.INT, SmedlType.CHAR, None]) or (
                other.type is None and self.type in [
                SmedlType.INT, SmedlType.CHAR]):
            return None
        # If one or both operands are int and all are int or char, return int
        elif (self.type == SmedlType.INT and other.type in [
                SmedlType.INT, SmedlType.CHAR]) or (
                other.type == SmedlType.INT and self.type == SmedlType.CHAR):
            return SmedlType.INT
        # If both operands are char, return char
        elif self.type == SmedlType.CHAR and other.type == SmedlType.CHAR:
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
        if (self.type in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR, None]
                and other.type in [SmedlType.INT, SmedlType.FLOAT,
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
        if self.type is None or other.type is None:
            return SmedlType.INT
        # If both operands are numbers, return int
        elif (self.type in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR] and
                other.type in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR]):
            return SmedlType.INT
        # If either operand is "null", the other can be "null", pointer, or
        # opaque. Return int
        elif (self.type == "null" and other.type in [
                SmedlType.POINTER, SmedlType.OPAQUE, "null"]) or (
                other.type == "null" and self.type in [
                SmedlType.POINTER, SmedlType.OPAQUE]):
            return SmedlType.INT
        # If both operands are the same type, return int
        elif self.type == other.type:
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
        # All numeric types are compatible with each other
        if (dest_type in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR] and
                self.type in [SmedlType.INT, SmedlType.FLOAT, SmedlType.CHAR,
                None]):
            return
        # All other types are compatible with themselves, None, and for POINTER
        # and OPAQUE, "null"
        elif (dest_type == SmedlType.STRING and self.type in [
                SmedlType.STRING, None]):
            return
        elif (dest_type == SmedlType.POINTER and self.type in [
                SmedlType.POINTER, "null", None]):
            return
        elif (dest_type == SmedlType.THREAD and self.type in [
                SmedlType.THREAD, None]):
            return
        elif (dest_type == SmedlType.OPAQUE and self.type in [
                SmedlType.OPAQUE, "null", None]):
            return
        # If none of the other cases matched, we have a type mismatch
        else:
            raise TypeMismatch("{} cannot be used as a {}".format(self.type,
                dest_type))

class StateVar(Expression):
    """A state variable usage"""
    def __init__(self, name, type_):
        super().__init__(type_)
        self.name = name
        self.type = type_

class EventParam(Expression):
    """An event parameter usage. Event parameters are referred to internally by
    their index in the parameter list, as the parameters can be given different
    names each time the event is used in a transition."""
    def __init__(self, idx, type_):
        super().__init__(type_)
        self.name = name

class Literal(Expression):
    """A literal in an expression"""
    def __init__(self, string, type_):
        """Initialize the literal.

        Parameters:
        string - The literal's representation in C syntax, e.g. "123" for an
          integer or "'a'" for a char
        type_ - The SMEDL type of the literal
        """
        super().__init__(type_)
        self.string = string

class HelperCall(Expression):
    """A call to a helper function in an expression"""
    def __init__(self, name, params):
        """Initialze the HelperCall.

        Parameters:
        name - The name of the helper function
        params - A list of expressions (types from this module) to be passed as
          parameters to the helper function
        """
        super().__init__(None)
        self.name = name
        self.params = params

class UnaryOp(Expression):
    """A unary operation in an expression"""
    def __init__(self, operator, operand):
        """Initialize the UnaryOp. Raise a TypeMismatch if the type is not
        compatible.

        Parameters:
        operator - The operator, as a string (e.g. "+", "-", "~", "!")
        operand - The operand, an expression type from this module
        """
        super().__init__(operand.unary_type_check(operator))
        self.operator = operator
        self.operand = operand

    def parenthesize(self):
        self.parens = True

class BinaryOp(Expression):
    """A binary operation in an expression"""
    def __init__(self, operator, left, right, type_):
        """Initialize the BinaryOp. Raise a TypeMismatch if the types are not
        compatible.

        Parameters:
        operator - The operator, as a string (e.g. "+", "/", ">>", "!=", etc.)
        left - The left operand, an expression from this module
        right - The right operand, an expression from this module
        """
        super().__init__(left.binary_type_check(operator, right))
        self.operator = operator
        self.left = left
        self.right = right

    def parenthesize(self):
        self.parens = True
