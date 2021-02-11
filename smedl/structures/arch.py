"""
Structures and types for monitoring system architectures (.a4smedl files)
"""

import sys
import types

from .expr import SmedlType
from smedl.parser.exceptions import (
        NameCollision, NameNotDefined, AlreadyInSyncset, ParameterError,
        DuplicateConnection, TypeMismatch, InternalError, ChannelMismatch)


class Parameter(object):
    """A parameter for a target specification. May be used for either monitor
    parameters, event parameters, or state var initializations. Specifies
    whether it comes from the source monitor or source event and an index in
    the source objects list of parameters."""
    def __init__(self, identity, index):
        """Initialize the Parameter.

        identity - Boolean. True if the parameter is a monitor parameter, also
          known as a monitor identity. False if it is an event parameter. Note:
          This is referring only to the source of the parameter! The
          destination depends only on where this parameter is used.
        index - The index in the monitor or event's parameter list that this
          parameter should come from.

        If this is to be a wildcard parameter for a monitor, index should be
        None.
        """
        self._identity = identity
        self._index = index
        # The Target that this parameter belongs to
        self._target = None

    @property
    def identity(self):
        """Return True if this is a monitor identity ("#x"), False if this is
        an event parameter ("$x")."""
        return self._identity

    @property
    def index(self):
        """Return None if this is a wildcard parameter ("*"). Otherwise, return
        the index of this parameter (the "x" in "$x" or "#x")."""
        return self._index

    @property
    def target(self):
        return self._target

    @target.setter
    def target(self, value):
        """Set the target if not already set"""
        if self._target is None:
            self._target = value
        else:
            raise InternalError("Adding more than one Target to a Parameter")

    @property
    def source_type(self):
        """Get the type of whichever parameter this Parameter is a reference
        to"""
        if self._index is None:
            raise InternalError(
                "Trying to take 'source_type' of a wildcard Parameter")
        if self._identity:
            return self._target.connection.source_mon.params[self._index]
        else:
            try:
                return self._target.connection.source_event_params[self._index]
            except BaseException as e:
                raise Exception() from e

    def __repr__(self):
        if self._index is None:
            return '*'
        elif self._identity:
            return '#' + str(self._index)
        else:
            return '$' + str(self._index)


class Target(object):
    """The target of a connection, such as an imported event or monitor
    creation. Note that this is not the same as the "target system," which is
    the system being monitored."""
    def __init__(self, type_, monitor, mon_params):
        """Initialize the Target object.

        type_ - String describing the type of target for Jinja
        monintor - DeclaredMonitor for the destination monitor, or None if this
          is a TargetExport
        mon_params - Iterable of Parameters for the monitor identities"""
        self._target_type = type_
        self._monitor = monitor
        for param in mon_params:
            param.target = self
        self._mon_params = tuple(mon_params)
        self._connection = None

    @property
    def target_type(self):
        """Get a string describing the type of target, for use in Jinja"""
        return self._target_type

    @property
    def monitor(self):
        """Get the destination DeclaredMonitor, or None if ExportTarget"""
        return self._monitor

    @property
    def mon_string(self):
        """Get the name of the destination DeclaredMonitor, or "pedl" if
        ExportTarget"""
        if self._monitor is None:
            return "pedl"
        else:
            return self._monitor.name

    @property
    def mon_params(self):
        """Get a tuple of Parameters for the monitor identities"""
        return self._mon_params

    @property
    def syncset(self):
        """Get the syncset that this Target belongs to"""
        return self._monitor.syncset

    @property
    def mon_params_w_types(self):
        """Get a sequence of (Parameter, SmedlType) tuples for the monitor
        identities"""
        return zip(self._mon_params, self._monitor.params)

    @property
    def connection(self):
        return self._connection

    @connection.setter
    def connection(self, conn):
        """Store a reference to the Connection this target belongs to"""
        if self._connection is None:
            self._connection = conn
        else:
            raise InternalError("Target already added to a connection")

    def __eq__(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        return self._monitor == other._monitor


class TargetEvent(Target):
    """An imported event connection target. Note that this is not the same as
    the "target system," which is the system being monitored."""
    def __init__(self, dest_monitor, dest_event, mon_params, event_params):
        """Initialize this target event.

        dest_monitor - DeclaredMonitor for the destination monitor
        dest_event - Name of the destination monitor's imported event
        mon_params - List of Parameters for the monitor identities
        event_params - List of Parameters for the event"""
        super().__init__('event', dest_monitor, mon_params)
        self._event = dest_event
        for param in event_params:
            param.target = self
        self._event_params = tuple(event_params)

    @property
    def event(self):
        """Get the name of the destination event"""
        return self._event

    @property
    def event_params(self):
        """Get a tuple of Parameters for the destination event"""
        return self._event_params

    @property
    def event_params_w_types(self):
        """Get a sequence of (Parameter, SmedlType) tuples for the destination
        event"""
        return zip(self._event_params,
                   self._monitor.spec.imported_events[self._event])

    def __eq__(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        if not isinstance(other, TargetEvent):
            return False
        return super().__eq__(other) and self._event == other._event

    def __repr__(self):
        mon_param_str = ', '.join([str(p) for p in self._mon_params])
        ev_param_str = ', '.join([str(p) for p in self._event_params])
        return ('TargetEvent:' + self._monitor.name + '[' + mon_param_str +
                '].' + self._event + '(' + ev_param_str + ')')


class TargetCreation(Target):
    """A monitor creation target. Note that this is not the same as the "target
    system," which is the system being monitored."""
    def __init__(self, dest_monitor, mon_params, state_vars):
        """Initialize this target creation event.

        dest_monitor - DeclaredMonitor for the monitor to be created
        mon_params - List of Parameters for the monitor identities. None may be
          wildcard parameters.
        state_vars - Dict containing any state variable initializations, where
          keys are state variable names and values are Parameters (which may
          not be wildcards).
        """
        super().__init__('creation', dest_monitor, mon_params)
        for param in state_vars.values():
            param.target = self
        self._state_vars = state_vars

    @property
    def state_vars(self):
        """Get a mapping of state var names to Parameters"""
        return types.MappingProxyType(self._state_vars)

    def __eq__(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        if not isinstance(other, TargetCreation):
            return False
        return super().__eq__(other)

    def __repr__(self):
        mon_param_str = ', '.join([str(p) for p in self._mon_params])
        state_var_str = ', '.join(
            [k + '=' + str(v) for k, v in self._state_vars.values()])
        return ('TargetCreation:' + self._monitor.name + '(' + mon_param_str +
                ', ' + state_var_str + ')')


class TargetExport(Target):
    """An event export target, for events that are exported out of a
    synchronous set back to the target system. Note that "export target" and
    "target system" are two different senses of the word "target," the former
    being a connection target and the latter being the target of monitoring."""
    def __init__(self, exported_event, event_params):
        """Initialize this export target with the given ExportedEvent and
        iterable of Parameters"""
        super().__init__('export', None, [])
        self._exported_event = exported_event
        self._event_params = tuple(event_params)

        # Export targets belong to synchronous sets directly
        self._syncset = None

    @property
    def exported_event(self):
        return self._exported_event

    @property
    def event(self):
        """Get the name for the exported event"""
        return self._exported_event.name

    @property
    def event_params(self):
        """Get a tuple of Parameters for the exported event"""
        return self._event_params

    @property
    def event_params_w_types(self):
        """Get a sequence of (Parameter, SmedlType) tuples for the exported
        event"""
        return zip(self._event_params,
                   self._exported_event.params)

    @property
    def syncset(self):
        """Get the syncset that this Target belongs to"""
        return self._syncset

    @syncset.setter
    def syncset(self, value):
        if self._syncset is not None:
            raise AlreadyInSyncset(
                "Event {} cannot be added to a synchronous set twice."
                .format(self._exported_event.name))
        self._syncset = value

    def __eq__(self, other):
        """Return true if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        return self._exported_event == other._exported_event

    def __repr__(self):
        # self.monitor should be None and self.mon_params empty, but printing
        # them will confirm
        mon_param_str = ', '.join([str(p) for p in self._mon_params])
        return ('TargetExport:' + self._exported_event)


class ExportedEvent(object):
    """An event exported back to the target system.

    Events imported from the target system have their name and parameter info
    stored in the relevant Connection object. Events to and from monitors have
    their info stored in a MonitorSpec object. This class stores the name and
    parameter info for events exported back to the target system, since it is
    not stored anywhere else.

    Parameters:
    name - Name of the event.
    params - List of SmedlType, or None if they should be inferred"""
    def __init__(self, name, params=None):
        self._name = name
        self._infer_params = (params is None)
        self._params = params

    @property
    def name(self):
        """Get the name of this ExportedEvent"""
        return self._name

    @property
    def params(self):
        """Get a sequence of SmedlType representing the event parameters"""
        return tuple(self._params)

    def check_params(self, conn, param_list):
        """Typecheck the given source parameters against this event's
        parameters, doing type inferral if necessary

        Parameters:
        conn - Connection that is routing to this ExportedEvent
        param_list - List of Parameters from the TargetExport"""
        source_ids = conn.source_mon.params
        source_params = conn.source_event_params

        if self._params is None:
            self._params = []
            for param in param_list:
                if param.identity:
                    try:
                        self._params.append(source_ids[param.index])
                    except IndexError:
                        raise ParameterError(
                            "Source monitor {} does not have identity {}"
                            .format(conn.source_mon.name, param.index))
                else:
                    try:
                        self._params.append(source_params[param.index])
                    except IndexError:
                        raise ParameterError(
                            "Source event {} does not have param {}"
                            .format(conn.source_event, param.index))
        else:
            if len(self._params) != len(param_list):
                raise ParameterError(
                    "Wrong number of parameters for dest event {}"
                    .format(self._name))
            for i, param in enumerate(param_list):
                if param.identity:
                    try:
                        param_type = source_ids[param.index]
                    except IndexError:
                        raise ParameterError(
                            "Source monitor {} does not have identity {}"
                            .format(conn.source_mon.name, param.index))
                    if not param_type.convertible_to(self._params[i]):
                        raise TypeMismatch(
                            "Param {} in source monitor {} does not match dest"
                            " {}".format(i, conn.source_mon.name, self._name))
                else:
                    try:
                        param_type = source_params[param.index]
                    except IndexError:
                        raise ParameterError(
                            "Source event {} does not have param {}"
                            .format(conn.source_event, param.index))
                    if not param_type.convertible_to(self._params[i]):
                        raise TypeMismatch(
                            "Param {} in source event {} does not match dest "
                            "{}".format(i, conn.source_event, self._name))

                self._params[i] = SmedlType.inference(param_type,
                                                      self._params[i])

    def __hash__(self):
        """Hash based on event name"""
        return hash(self._name)

    def __eq__(self, other):
        """Compare for equality based on event name"""
        if not isinstance(other, ExportedEvent):
            return NotImplemented
        return self._name == other._name

    def __repr__(self):
        if self._infer_params and self._params is None:
            return "{}(Inferred: ...)".format(self._name)
        elif self._infer_params:
            return "{}(Inferred: {})".format(self._name,
                                             ", ".join(self._params))
        else:
            return "{}({})".format(self._name, ", ".join(self._params))


class Connection(object):
    """A connection between a source event and some number of targets"""
    def __init__(self, sys, source_mon, source_event,
                 source_event_params=None):
        """Create a connection with the specified source monitor and event.

        sys - Monitoring system
        source_mon - Source monitor decl, or None if from the target system.
        source_event - Source event name
        source_event_params - An iterable of SmedlTypes for the source event's
          parameters. Only used for events from the target system and if the
          event was declared in the architecture file.
        """
        # The channel name
        self._channel = None
        # The MonitorSystem this connection is part of
        self._sys = sys
        # The source DeclaredMonitor for this connection (or None if from the
        # target system)
        self._source_mon = source_mon
        # The source event name for this connection
        self._source_event = source_event
        # Synchronous set this connection belongs to (only applies to
        # connections from the target system, i.e. source_mon is None)
        self._syncset = None
        # A list of Targets that this connection links to
        self._targets = []
        # Need to store the source event param types here when there is no
        # source monitor to provide them.
        # Keys for self._source_ev_params are int (source param index), values
        # are SmedlType
        if source_mon is None:
            if source_event_params is None:
                # If the event was not declared in the architecture file, we
                # need to infer the source parameter types.
                self._infer_source_params = True
                self._source_ev_params = dict()
            else:
                # Otherwise, use source_event_params to populate the dict.
                self._infer_source_params = False
                self._source_ev_params = dict(zip(
                    range(len(source_event_params)), source_event_params))

    @property
    def channel(self):
        return self._channel

    @property
    def source_mon(self):
        return self._source_mon

    @property
    def mon_string(self):
        """If there is a source monitor, return its name. If not, return the
        string "pedl"."""
        if self._source_mon is None:
            return "pedl"
        else:
            return self._source_mon.name

    @property
    def source_event(self):
        return self._source_event

    @property
    def source_event_params(self):
        """Return a sequence of the source event params' SmedlTypes (or for a
        connection from the target system, None for those that are not
        known)"""
        if self._source_mon is None:
            result = list()
            for i in range(max(self._source_ev_params.keys()) + 1):
                result.append(self._source_ev_params.get(i))
            return result
        else:
            return self._source_mon.spec.exported_events[self._source_event]

    @property
    def event_params_inferred(self):
        """Return True if source_event_params was determined through inferral,
        false if from monitor specifications or event declarations."""
        return self._source_mon is None and self._infer_source_params

    @property
    def syncset(self):
        """If the source event is from the target system, get the syncset it
        belongs to (if it has been set yet). Otherwise, return None."""
        return self._syncset

    @syncset.setter
    def syncset(self, value):
        if self._source_mon is not None:
            raise InternalError("Tried to add a Connection that's not from "
                                "the target system to a synchronous set")
        if self._syncset is not None:
            raise AlreadyInSyncset(
                "Event {} cannot be added to a synchronous set twice."
                .format(self._source_event))
        self._syncset = value

    @property
    def targets(self):
        return self._targets

    @property
    def inter_syncsets(self):
        """Return a sequence of the SynchronousSets the source event is routed
        to, not including its own."""
        source_set = (self._syncset if self._source_mon is None else
                      self._source_mon.syncset)
        sets = []
        for target in self._targets:
            if target.monitor is None:
                dest_set = target.syncset
            else:
                dest_set = target.monitor.syncset
            if dest_set != source_set and dest_set not in sets:
                sets.append(dest_set)
        return sets

    def __eq__(self, other):
        """Test for equality with source monitor and event"""
        if isinstance(other, Connection):
            return (self.source_mon == other.source_mon and
                    self.source_event == other.source_event)
        else:
            return False

    def __hash__(self):
        """Hash by source monitor and event"""
        return hash((self._source_mon, self._source_event))

    def assign_name(self, channel):
        """If the channel name given is not None, validate that it doesn't
        conflict with a previously assigned name for the same channel, then
        assign it.
        """
        if channel is None:
            # Channel not specified
            return
        elif self._channel is None:
            # No previous channel name. Use the given one.
            self._channel = channel
            if self._source_mon is None:
                self._sys.rename_connection(self)
            else:
                self._source_mon.rename_connection(self)
        elif self._channel != channel:
            # Previously assigned channel name does not match. Raise exception.
            if self._source_mon is None:
                event_str = self._source_event
            else:
                event_str = (self._source_mon.name + '.' + self._source_event)
            raise ChannelMismatch("Source event {} must always use the same "
                                  "connection name".format(event_str))

    def assign_default_name_if_unnamed(self):
        """Assign a default name to this channel if it's still unnamed:
        - <event> (events from target system)
        - <monitor>_<event> (events from monitor)

        If the default is already taken, append "_2", "_3", etc. until an
        available name is found"""
        if self._channel is not None:
            return
        if self._source_mon is None:
            name = self._source_event
        else:
            name = self._source_mon.name + "_" + self._source_event

        self._channel = name
        num = 1
        while True:
            try:
                if self._source_mon is None:
                    self._sys.rename_connection(self)
                else:
                    self._source_mon.rename_connection(self)
            except NameCollision:
                num += 1
                self._channel = name + "_" + str(num)
            else:
                break

    def _typecheck_dest_param(self, dest_param, dest_type, dest_name):
        """Do type verification on a single destination Parameter.

        If this connection is from the target system, the actual parameter
        types are unknown, but if the same parameter is used in multiple
        destinations, verify that it matches. And store the type for later
        use by templates.

        dest_param - The Parameter to verify
        dest_type - The SmedlType to verify against
        dest_name - Name of what's being typechecked, e.g. "parameter ___ of
          event ___" or "state var ___ of monitor ___", to be used in exception
          messages
        """
        # Wilcdard params match any type
        if dest_param.index is None:
            return

        # Identity params ("#x"/"Id.x")
        if dest_param.identity:
            if self._source_mon is None:
                raise ParameterError(
                    'Cannot use identity parameters ("Id."/"#") for {} when '
                    'there is no source monitor'.format(dest_name))
            else:
                try:
                    source_type = self._source_mon.params[dest_param.index]
                except IndexError:
                    raise ParameterError(
                        "Source monitor {} does not have identity {}"
                        .format(self._source_mon.name, dest_param.index))
                if not source_type.convertible_to(dest_type):
                    raise TypeMismatch(
                        "Param {} in source monitor {} does not match dest {}"
                        .format(dest_param.index, self._source_mon.name,
                                dest_name))

        # Event params ("$x"/"Param.x")
        else:
            if self._source_mon is None:
                try:
                    source_type = self._source_ev_params[dest_param.index]
                except KeyError:
                    if self._infer_source_params:
                        # Type inference: Store the destination param type
                        self._source_ev_params[dest_param.index] = dest_type
                        return
                    else:
                        raise ParameterError(
                            "Source event {} does not have parameter {}"
                            .format(self._source_event, dest_param.index))
                if not source_type.convertible_to(dest_type):
                    raise TypeMismatch(
                        "Param {} in source event {} does not match dest {}"
                        .format(dest_param.index, self._source_event,
                                dest_name))
                elif self._infer_source_params:
                    # Type inference: If the types don't match, use the one
                    # that takes precedence
                    self._source_ev_params[dest_param.index] = (
                        SmedlType.inference(source_type, dest_type))
            else:
                source_ev_params = self._source_mon.spec.exported_events[
                        self._source_event]
                try:
                    source_type = source_ev_params[dest_param.index]
                except IndexError:
                    raise ParameterError(
                        "Source event {} does not have parameter {}"
                        .format(self._source_mon.name,
                                dest_param.index))
                if not source_type.convertible_to(dest_type):
                    raise TypeMismatch(
                        "Param {} in source event {} does not match dest {}"
                        .format(dest_param.index, self._source_event,
                                dest_name))

    def _typecheck_dest_params(self, dest_params, dest_param_types, dest_name):
        """Do type verification on a destination parameter list from this
        connection's source monitor and event parameters.

        If this connection is from the target system, the actual parameter
        types are unknown, but if the same parameter is used in multiple
        destinations, verify that it matches. And store the type for later
        use by templates.

        dest_params - An iterable of Parameters
        dest_param_types - The SmedlTypes of the dest_params
        dest_name - Name of what's being typechecked, e.g. "monitor ___"
          or "event ___", to be used in exception messages
        """
        for i in range(len(dest_params)):
            self._typecheck_dest_param(dest_params[i], dest_param_types[i],
                                       "param {} in {}".format(i, dest_name))

    def _typecheck_target(self, target):
        """Do type verification on all monitor identities, event parameters,
        and state variables in the provided Target"""
        # Typecheck monitor params
        if target.monitor is not None:
            self._typecheck_dest_params(
                target.mon_params, target.monitor.params,
                "monitor " + target.monitor.name)

        if isinstance(target, TargetEvent):
            # Typecheck destination event parameter types
            self._typecheck_dest_params(
                target.event_params,
                target.monitor.spec.imported_events[target.event],
                "event " + target.event)
        elif isinstance(target, TargetCreation):
            # Typecheck destination state var types
            for var, param in target.state_vars.items():
                var_type = target.monitor.spec.state_vars[var].type
            self._typecheck_dest_param(
                param, var_type, "state var {} of monitor {}".format(
                    var, target.monitor.name))
        elif isinstance(target, TargetExport):
            # Typecheck destination PEDL event types
            target.exported_event.check_params(self, target.event_params)

    def add_target(self, target):
        """Add a Target to this channel after verifying that it is not a
        duplicate of any targets it already contains and typechecking all
        its parameters/state vars"""
        for t in self._targets:
            if target == t:
                #TODO I think this is checking for duplicate destinations, not
                # source and destination are the same. But both tests are
                # important. Make sure both happen and fix the exception msg.
                raise DuplicateConnection(
                    "Source and destination of connections cannot match.")
        self._typecheck_target(target)
        self._targets.append(target)
        target.connection = self

    def __repr__(self):
        if self._source_mon is None:
            return "Connection({}: {} => ...)".format(
                self._channel, self._source_event)
        else:
            return "Connection({}: {}.{} => ...)".format(
                self._channel, self._source_mon.name, self._source_event)


class SynchronousSet(set):
    """A subclass of set customized to represent a Synchronous Set.
    Meant to contain DeclaredMonitor, Connection (only when originating at the
    target system), and ExportedEvent."""
    def __init__(self, name, *args, **kwargs):
        """Create a new SynchronousSet"""
        self._name = name
        super().__init__(*args, **kwargs)

    @property
    def name(self):
        """Get the name of the synchronous set"""
        return self._name


class DeclaredMonitor(object):
    """A monitor delcaration from the architecture file"""
    def __init__(self, sys, name, spec, params):
        # The monitoring system this DeclaredMonitor belongs to
        self._sys = sys
        # Name of the monitor given in the declaration (meaning the "as" name,
        # if provided)
        self._name = name
        # The monitor.MonitorSpec to use for this monitor
        self._spec = spec
        # Tuple of the parameter types to use for this monitor (as SmedlTypes)
        self._params = tuple(params)
        # Reference to this monitor's synchronous set
        self._syncset = None
        # Connections that originate from this monitor. Keys are channel names.
        # Values are Connections.
        self._connections = dict()
        # Same as above, but using event names as the key, instead.
        self._ev_connections = dict()

    @property
    def name(self):
        """Get the given name ("as" name) of this monitor"""
        return self._name

    @property
    def spec(self):
        """Get the MonitorSpec for this monitor"""
        return self._spec

    @property
    def params(self):
        """Get a tuple of the identity params for this monitor (as
        SmedlTypes)"""
        return self._params

    @property
    def syncset(self):
        """Get the SynchronousSet that this monitor belongs to"""
        return self._syncset

    @property
    def connections(self):
        """Get this monitor's connections indexed by channel name"""
        return types.MappingProxyType(self._connections)

    @property
    def ev_connections(self):
        """Get this monitor's connections indexed by source event name"""
        return types.MappingProxyType(self._ev_connections)

    def __eq__(self, other):
        """Test for equality with the monitor name"""
        if isinstance(other, DeclaredMonitor):
            return self._name == other.name
        else:
            return False

    def __hash__(self):
        """Hash by monitor name"""
        return hash(self._name)

    def assign_syncset(self, syncset):
        """Assign the monitor to a synchronous set. If it is already in one,
        raise AlreadyInSyncset"""
        if self._syncset is not None:
            raise AlreadyInSyncset(
                "Monitor {} cannot be added to a synchronous set twice."
                .format(self.name))
        self._syncset = syncset

    def add_target(self, channel, source_event, target):
        """Add the given target to the proper connection for the source event
        (creating the connection if it does not exist yet).

        channel - Channel name, or None to use the default (the name used in
          another connection for this source event, or autogenerated if none)
        source_event - Name of the source event
        target - A Target object
        """
        # Check that source event exists and get the params
        if source_event not in self._spec.exported_events:
            raise NameNotDefined("Source monitor {} does not contain exported "
                                 "event {}".format(self._name, source_event))

        # Get or create Connection
        try:
            conn = self._ev_connections[source_event]
        except KeyError:
            conn = Connection(self._sys, self, source_event)
            self._ev_connections[source_event] = conn

        # Validate the channel name and name the channel (also calls
        # rename_connection() to update the _connections dict)
        conn.assign_name(channel)

        # Add the target to the channel, if it's not a duplicate
        conn.add_target(target)

    def rename_connection(self, conn):
        """Put the given connection in the _connections dict under the correct
        name. Called by Connection when it is assigned an automatic or explicit
        name."""
        if self._sys.channel_name_taken(conn.channel):
            raise NameCollision("Channel name {} must always be used for the "
                                "same source event".format(conn.channel))
        self._connections[conn.channel] = conn

    def create_export_connections(self):
        """Exported events that are not explicitly the source of a connection
        in the architecture specification implicitly get exported back to the
        environment. This creates those implicit TargetExports."""
        exported_events = []
        for event, params in self._spec.exported_events.items():
            if event not in self._ev_connections:
                conn = Connection(self._sys, self, event)
                self._ev_connections[event] = conn

                name = "_{}_{}".format(self._name, event)
                exported_event = ExportedEvent(name)
                exported_events.append(exported_event)
                parameters = [Parameter(False, i) for i in range(len(params))]
                conn.add_target(TargetExport(exported_event, parameters))
        return exported_events

    def name_unnamed_channels(self):
        """Assign default channel names to any remaining unnamed channels in
        the monitor: <monitor>_<event>
        A "_<#>" will be appended if the default name is already used
        """
        for conn in self._ev_connections.values():
            conn.assign_default_name_if_unnamed()

    # TODO intra_connections and inter_connections still needed?
    @property
    def intra_connections(self):
        """Return a list of connections where this monitor is the source and
        at least one destination is in the same synchronous set"""
        result = []
        for conn in self._connections.values():
            for target in conn.targets:
                if target.monitor is None:
                    if target.syncset is self._syncset:
                        result.append(conn)
                        break
                elif target.monitor in self._syncset:
                    result.append(conn)
                    break
        return result

    @property
    def inter_connections(self):
        """Return a list of connections where this monitor is the source and
        at least one destination is not in the same synchronous set"""
        result = []
        for conn in self._connections.values():
            for target in conn.targets:
                if target.monitor is None:
                    if target.syncset is not self._syncset:
                        result.append(conn)
                        break
                elif target.monitor not in self._syncset:
                    result.append(conn)
                    break
        return result

    def __repr__(self):
        return "monitor {}({}) as {}".format(
            self._spec.name, ", ".join([str(p) for p in self._params]),
            self._name)


class MonitorSystem(object):
    """A monitor system as specified by an architecture file (a4smedl file)"""
    def __init__(self):
        self._name = None

        # Monitor declarations. Keys are the "as X" names of the monitors,
        # values are DeclaredMonitors
        self._monitor_decls = dict()

        # Synchronous sets. Keys are names of synchronous sets. Values are
        # SynchronousSets (named sets of DeclaredMonitors)
        self._syncsets = dict()

        # Connections whose source are the target system:
        # Using channel names as keys
        self._imported_connections = dict()
        # Using source event names as keys
        self._ev_imported_connections = dict()
        # Values are Connections.

        # Events destined for the target system. Keys are event names. Values
        # are ExportedEvents
        self._exported_events = dict()

    @property
    def name(self):
        return self._name

    @name.setter
    def name(self, value):
        if self._name is None:
            self._name = value
        else:
            raise InternalError("Monitoring system already named")

    @property
    def monitor_decls(self):
        return types.MappingProxyType(self._monitor_decls)

    @property
    def syncsets(self):
        return types.MappingProxyType(self._syncsets)

    @property
    def imported_connections(self):
        return self._imported_connections

    @property
    def ev_imported_connections(self):
        return self._ev_imported_connections

    def __eq__(self, other):
        """Test for equality with the system name"""
        if isinstance(other, MonitorSystem):
            return self.name is not None and self.name == other.name
        else:
            return False

    def add_syncset(self, name, members):
        """Add a synchronous set to the system.

        Parameters:
        name - Name of the synchronous set
        members - An iterable of dicts representing the monitors and PEDL
          events to be added to this synchronous set. Each dict must contain
          two keys: 'kind' and 'name'. The 'kind' is one of the following:
            * 'monitor' - The member is a monitor
            * 'imported' - The member is an imported PEDL event
            * 'exported' - The member is an exported PEDL event
          and 'name' is the name of the monitor or event. Monitors must already
          be declared and all of the given members must not already be in a
          synchronous set.
        """
        # Ensure the synchronous set does not already exist
        if name in self._syncsets:
            raise NameCollision(
                "Synchronous set {} is already defined".format(name))

        # Create the SynchronousSet
        syncset = SynchronousSet(name)

        # Iterate through the members.
        # For monitors: Check if they exist, check if they are already in a
        #   synchronous set, and assign them to the new synchronous set
        # For PEDL events: Check if the event exists. If so, make sure its
        #   Connection/ExportedEvent is not in another synchronous set and add
        #   it. If not, create a Connection/ExportedEvent and add it.
        for member in members:
            kind = member['kind']
            member_name = member['name']
            if kind == 'monitor':
                try:
                    self._monitor_decls[member_name].assign_syncset(syncset)
                except KeyError:
                    raise NameNotDefined(
                        "Monitor {} has not been declared".format(member_name))
                syncset.add(self._monitor_decls[member_name])
            elif kind == 'imported':
                try:
                    self._ev_imported_connections[member_name].syncset = \
                        syncset
                except KeyError:
                    conn = Connection(self, None, member_name)
                    self._ev_imported_connections[member_name] = conn
                    conn.syncset = syncset
                syncset.add(self._ev_imported_connections[member_name])
            elif kind == 'exported':
                try:
                    self._exported_events[member_name].syncset = syncset
                except KeyError:
                    exported_ev = ExportedEvent(member_name)
                    self._exported_events[member_name] = exported_ev
                    exported_ev.syncset = syncset
                syncset.add(self._exported_events[member_name])
            else:
                raise InternalError('Syncset "{}" conatain member "{}" with '
                                    'unknown kind "{}"'.format(
                                        name, member_name, kind))

        # Add the syncset to the MonitorSystem
        self._syncsets[name] = syncset

    def _unused_syncset(self, name):
        """Find an unused synchronous set name for the given name. If the name
        iself is not already a synchronous set, use that. Otherwise, append a
        number."""
        syncset = name
        i = 1
        while syncset in self._syncsets:
            i += 1
            syncset = name + str(i)
        if syncset != name:
            if name == 'PEDL':
                print("Warning: 'PEDL' is already the name of a synchronous "
                      "set. Using {} for the syncset containing asynchronous "
                      "PEDL events.".format(syncset), file=sys.stderr)
            else:
                print("Warning: {0} is already the name of a synchronous set. "
                      "Monitor {0} will be in synchronous set {1}"
                      .format(name, syncset), file=sys.stderr)
        return syncset

    def add_connection(self, source_ev, params):
        """Add an empty connection for a source event from the target system

        source_ev - Name of the source event
        params - An iterable of SmedlType for the event's parameters
        """
        # Check if it already exists
        if source_ev in self._ev_imported_connections:
            raise NameCollision("Event {} cannot be declared multiple times "
                                "or after it has already been used implicitly"
                                .format(source_ev))

        # Create it
        conn = Connection(self, None, source_ev, params)
        self._ev_imported_connections[source_event] = conn

    def add_target(self, channel, monitor, source_event, target):
        """Add the given target to the proper connection for the source event
        (creating the connection if it does not exist yet).

        channel - Channel name, or None to use the default (the name used in
          another connection for this source event, or autogenerated if none)
        monitor - Declared monitor name, or None if from the target system
        source_event - Name of the source event
        target - A Target object
        """
        # If from a monitor, call that monitor's add_target
        if monitor is not None:
            try:
                decl = self._monitor_decls[monitor]
            except KeyError:
                raise NameNotDefined("Source monitor {} is not declared"
                                     .format(monitor))
            decl.add_target(channel, source_event, target)
            return

        # Get or create Connection
        try:
            conn = self._ev_imported_connections[source_event]
        except KeyError:
            conn = Connection(self, None, source_event)
            self._ev_imported_connections[source_event] = conn

        # Validate the channel name and name the channel (also calls
        # rename_connection() to update the _imported_connections dict)
        conn.assign_name(channel)

        # Add the target to the channel, if it's not a duplicate
        conn.add_target(target)

    def rename_connection(self, conn):
        """Put the given connection in the _imported_connections dict under the
        correct name. Called by Connection when it is assigned an automatic or
        explicit name."""
        if self.channel_name_taken(conn.channel):
            raise NameCollision("Channel name {} must always be used for the "
                                "same source event".format(conn.channel))
        self._imported_connections[conn.channel] = conn

    def channel_name_taken(self, channel):
        """Return True if the channel name is already used, False otherwise"""
        if channel in self._imported_connections:
            return True
        for decl in self._monitor_decls.values():
            if channel in decl.connections:
                return True
        return False

    def add_monitor_decl(self, name, target, params):
        """Add a monitor declaration to the system.

        Parameters:
        name - Name given to the monitor (i.e. the "as" name, if provided, or
          the regular name if not)
        target - a MonitorSpec for an imported monitor this name was assigned
          to
        params - A list of SmedlType representing the parameters (identities)
          of this monitor
        """
        # Monitors can't be named "pedl"
        if name == 'pedl':
            raise NameCollision("Monitors cannot be named 'pedl'")
        # Check if the given name is already taken
        if name in self.monitor_decls:
            raise NameCollision(
                "Monitor name {} is already declared".format(name))

        # Create and store the DeclaredMonitor
        self._monitor_decls[name] = DeclaredMonitor(self, name, target, params)

    def assign_singleton_syncsets(self):
        """Assign any monitors that are not already in a synchronous set to
        their own isolated synchronous sets. Normally, these synchronous sets
        will be named after the monitor, but if that name is already taken,
        a warning will be displayed and a number appended."""
        for mon in self._monitor_decls.values():
            if mon.syncset is None:
                syncset = self._unused_syncset(mon.name)
                self.add_syncset(syncset, ({'kind': 'monitor',
                                            'name': mon.name},))

    def finalize_pedl_events(self):
        """Check events from the target system for two things:
        1. Events that were declared but not used (print a warning)
        2. Events from the target system that are not yet in a synchronous set.
           If there are any, create a PEDL synchronous set for them, named
           "PEDL" (or "PEDL2" etc. if "PEDL" was taken)
        In addition, check for exported monitor events that are not the source
        of a connection. For these, create implicit Connections and
        ExportedEvents and add them to the PEDL syncset as well.
        """
        pedl_evs_without_syncset = []

        # Check (1) and (2) from docstring
        for conn in self._ev_imported_connections.values():
            if conn.channel is None
                print("Warning: Event {} was not used in a connection"
                      .format(conn.source_event), file=sys.stderr)
            else:
                #TODO Do unused connections need to go into the syncset too?
                # Probably. If it was declared, we should be prepared to accept
                # it and do nothing.
                if conn.syncset is None:
                    pedl_evs_without_syncset.append(
                        {'kind': 'imported', 'name': conn.source_event})

        # Do last part of docstring (unconnected exported monitor events)
        for mon in self._monitor_decls.values():
            exported_events = mon.create_export_connections()
            for ev in exported_events:
                pedl_evs_without_syncset.append(
                    {'kind': 'exported', 'name': ev.name})

        if len(pedl_evs_without_syncset) > 0:
            syncset_name = self._unused_syncset('PEDL')
            self.add_syncset(syncset_name, pedl_evs_without_syncset)

    def name_unnamed_channels(self):
        """Assign default channel names to any remaining unnamed channels in
        the system and all its DeclaredMonitors:
        - <event> for events from the target system
        - <monitor>_<event> for events from monitors

        A "_<#>" will be appended if the default name is already used
        """
        # Assign names to unnamed channels from the target system
        for conn in self._ev_imported_connections.values():
            conn.assign_default_name_if_unnamed()

        # Assign names to unnamed channels from monitors
        for mon in self._monitor_decls.values():
            mon.name_unnamed_channels()

    def complete_system(self):
        """Complete the MonitorSystem by performing actions that could not be
        done before the entire architecture file has been processed:
        - Assign monitors that are not yet in synchronous sets to singleton
          synchronous sets
        - Create a synchronous set for PEDL events, if there are any unassigned
        - Create connections to the target system for exported events that are
          not in any other connection
        - Assign default names to connections that are still unnamed
        """
        self.assign_singleton_syncsets()
        self.finalize_pedl_events()
        self.name_unnamed_channels()

    def imported_channels(self, syncset):
        """Get a list of Connections with sources not in the given synchronous
        set and destinations in it

        syncset - Name of the synchronous set"""
        result = []

        # Sort through the channels from the target system
        for conn in self._imported_connections.values():
            if conn in self._syncsets[syncset]:
                continue
            for target in conn.targets:
                if target.monitor in self._syncsets[syncset]:
                    result.append(conn)
                    break

        # Sort through channels from monitors
        for decl in self._monitor_decls.values():
            if decl in self._syncsets[syncset]:
                continue
            for conn in decl.connections.values():
                for target in conn.targets:
                    if target.monitor is None:
                        if target.event in self._syncsets[syncset]:
                            result.append(conn)
                            break
                    elif target.monitor in self._syncsets[syncset]:
                        result.append(conn)
                        break

        return result

    def dest_channels(self, syncset):
        """Get all Connections with destinations in the given synchronous set
        and return a dict, Connection -> list of Targets in syncset

        syncset - Name of the synchronous set"""
        result = {}

        # Sort through the channels from the target system
        for conn in self._imported_connections.values():
            targets = []
            for target in conn.targets:
                if target.monitor in self._syncsets[syncset]:
                    targets.append(target)
            if targets:
                result[conn] = targets

        # Sort through channels from monitors
        for decl in self._monitor_decls.values():
            for conn in decl.connections.values():
                targets = []
                for target in conn.targets:
                    if target.monitor is None:
                        if target.event in self._syncsets[syncset]:
                            targets.append(target)
                    elif target.monitor in self._syncsets[syncset]:
                        targets.append(target)
                if targets:
                    result[conn] = targets

        return result

    def syncset_spec_names(self, syncset):
        """Get a set of the MonitorSpec names for the named syncset

        syncset - Name of the synchronous set"""
        result = set()
        for obj in self._syncsets[syncset]:
            try:
                result.add(obj.spec.name)
            except AttributeError:
                # This obj is not a monitor
                pass
        return result
