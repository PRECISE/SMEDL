"""
Exceptions to represent various parsing and semantics errors
"""

#from tatsu.exceptions import FailedSemantics

class NameCollision(Exception):
    """Raised when a name is defined when it already exists."""
    pass

class TypeMismatch(Exception):
    """Raised when the type of an expression does not match what is expected."""
    pass

class NameNotDefined(Exception):
    """Raised when an identifier is used (e.g. event name, state variable, etc.)
    without being defined."""
    pass

class ElseCollision(Exception):
    """Raised when an else is provided for a state/event pair that already had
    an else."""
    pass

class AlreadyInSyncset(Exception):
    """Raised when a DeclaredMonitor is added to a synchronous set when it is
    already part of one."""
    pass

class ParameterError(Exception):
    """Raised when there is an issue with monitor or event parameters besides
    type, e.g. incorrect number of params or wildcard not allowed."""

class ChannelMismatch(Exception):
    """Raised when the different channel names are used for the same source
    event."""

class DuplicateConnection(Exception):
    """Raised when a connection is a duplicate of another (same source and
    destination, ignoring parameters)"""
