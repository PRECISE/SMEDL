"""
Exceptions to represent various parsing and semantics errors
"""

#from tatsu.exceptions import FailedSemantics

class InternalError(Exception):
    """Raised if an internal error occurs during parsing. If that ever happens,
    there is a bug."""

class SmedlException(Exception):
    """Base class for all SMEDL exceptions"""

class NameCollision(SmedlException):
    """Raised when a name is defined when it already exists."""

class TypeMismatch(SmedlException):
    """Raised when the type of an expression does not match what is expected."""

class NameNotDefined(SmedlException):
    """Raised when an identifier is used (e.g. event name, state variable, etc.)
    without being defined."""

class ElseCollision(SmedlException):
    """Raised when an else is provided for a state/event pair that already had
    an else."""

class AlreadyInSyncset(SmedlException):
    """Raised when a DeclaredMonitor is added to a synchronous set when it is
    already part of one."""

class ParameterError(SmedlException):
    """Raised when there is an issue with monitor or event parameters besides
    type, e.g. incorrect number of params or wildcard not allowed."""

class ChannelMismatch(SmedlException):
    """Raised when the different channel names are used for the same source
    event."""

class DuplicateConnection(SmedlException):
    """Raised when a connection is a duplicate of another (same source and
    destination, ignoring parameters)"""
