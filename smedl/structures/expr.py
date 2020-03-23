"""
Types for expression trees
"""

from enum import Enum

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
# The code that initializes instances of these classes is responsible for type
# checking. Every instance of these classes has a "type" property to facilitate
# that.

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
    def __init__(self, operator, operand, type_):
        """Initialize the UnaryOp.

        Parameters:
        operator - The operator, as a string (e.g. "+", "-", "~", "!")
        operand - The operand, an expression type from this module
        type_ - The SMEDL type of this expression
        """
        super().__init__(type_)
        self.operator = operator
        self.operand = operand

    def parenthesize(self):
        self.parens = True

class BinaryOp(Expression):
    """A binary operation in an expression"""
    def __init__(self, operator, left, right, type_):
        """Initialize the UnaryOp.

        Parameters:
        operator - The operator, as a string (e.g. "+", "/", ">>", "!=", etc.)
        left - The left operand, an expression from this module
        right - The right operand, an expression from this module
        type_ - The SMEDL type of this expression
        """
        super().__init__(type_)
        self.operator = operator
        self.left = left
        self.right = right

    def parenthesize(self):
        self.parens = True
