"""
Exceptions to represent various parsing and semantics errors
"""

from grako.exceptions import FailedSemantics

class NameCollision(FailedSemantics):
    """Raised when a name is defined when it already exists."""
    pass

class TypeMismatch(FailedSemantics):
    """Raised when the type of an expression does not match what is expected."""
    pass

class NameNotDefined(FailedSemantics):
    """Raised when an identifier is used (e.g. event name, state variable, etc.)
    without being defined."""
    pass

class ElseCollision(FailedSemantics):
    """Raised when an else is provided for a state/event pair that already had
    an else."""
    pass
