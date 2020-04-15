"""
Exceptions to represent various parsing and semantics errors
"""

from tatsu.exceptions import FailedSemantics

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

class AlreadyInSyncset(FailedSemantics):
    """Raised when a DeclaredMonitor is added to a synchronous set when it is
    already part of one."""
    pass

class ParameterError(FailedSemantics):
    """Raised when there is an issue with monitor or event parameters besides
    type, e.g. incorrect number of params or wildcard not allowed."""

class ChannelMismatch(FailedSemantics):
    """Raised when the different channel names are used for the same source
    event."""

class DuplicateConnection(FailedSemantics):
    """Raised when a connection is a duplicate of another (same source and
    destination, ignoring parameters)"""
