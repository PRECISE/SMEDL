"""
Structures and types for monitoring system architectures (.a4smedl files)
"""

import types
from smedl.parser.exceptions import (NameCollision, NameNotDefined,
        AlreadyInSyncset, ParameterError, DuplicateConnection, TypeMismatch,
        DuplicateConnection)

class Parameter(object):
    """A parameter for a target specification. May be used for either monitor
    parameters, event parameters, or state var initializations. Specifies
    whether it comes from the source monitor or source event and an index in
    the source objects list of parameters."""
    def __init__(self, identity, index):
        """Initialize the Parameter.

        identity - Boolean. True if the parameter is a monitor parameter, also
          known as a monitor identity. False if it is an event parameter. Note:
          This is referring only to the source of the parameter! The destination
          depends only on where this parameter is used.
        index - The index in the monitor or event's parameter list that this
          parameter should come from.

        If this is to be a wildcard parameter for a monitor, index should be
        None.
        """
        self._identity = identity
        self._index = index

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
        self._mon_params = tuple(mon_params)
        self._connection = None

    @property
    def target_type(self):
        """Get a string describing the type of target, for use in Jinja"""
        return self._target_type

    @property
    def monitor(self):
        """Get the name of the destination monitor, or None if ExportTarget"""
        return self._monitor

    @property
    def mon_params(self):
        """Get a tuple of Parameters for the monitor identities"""
        return self._mon_params

    @property
    def connection(self):
        return self._connection

    @connection.setter
    def connection(self, conn):
        """Store a reference to the Connection this target belongs to"""
        if self._connection is None:
            self._connection = conn
        else:
            raise Exception("Internal error: Target already added to a "
                    "connection")

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
        self._event_params = tuple(event_params)

    @property
    def event(self):
        """Get the name of the destination event"""
        return self._event

    @property
    def event_params(self):
        """Get a tuple of Parameters for the destination event"""
        return self._event_params

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
        state_var_str = ', '.join([k + '=' + str(v)
                for k, v in self._state_vars.values()])
        return ('TargetCreation:' + self._monitor.name + '(' + mon_param_str +
                ', ' + state_var_str + ')')

class TargetExport(Target):
    """An event export target, for events that are exported out of a synchronous
    set back to the target system. Note that "export target" and "target system"
    are two different senses of the word "target," the former being a connection
    target and the latter being the target of monitoring."""
    def __init__(self):
        """Initialize this export target."""
        super().__init__('export', None, [])

    def __eq__(self, other):
        """Return true if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        return isinstance(other, TargetExport)
    
    def __repr__(self):
        # self.monitor should be None and self.mon_params empty, but printing
        # them will confirm
        mon_param_str = ', '.join([str(p) for p in self._mon_params])
        return ('TargetExport:' + str(self._monitor) +
                '(' + mon_param_str + ')')

class Connection(object):
    """A connection between a source event and some number of targets"""
    def __init__(self, sys, source_mon, source_event):
        """Create a connection with the specified source monitor and event.
        
        sys - Monitoring system
        source_mon - Source monitor decl, or None if from the target system.
        source_event - Source event name
        """
        # The channel name
        self._channel = None
        # The MonitorSystem this connection is part of
        self._sys = sys
        # The source DeclaredMonitor for this connection (or None if from the
        # target system)
        self._source_mon = None
        # The source event name for this connection
        self._source_event = None
        # A list of Targets that this connection links to
        self._targets = []

    @property
    def channel(self):
        return self._channel

    @property
    def source_mon(self):
        return self._source_mon

    @property
    def source_event(self):
        return self._source_event

    @property
    def targets(self):
        return self._targets

    def __eq__(self, other):
        """Test for equality with the channel name"""
        if isinstance(other, Connection):
            return self.channel is not None and self.channel == other.channel
        else:
            return False

    def assign_name(self, channel):
        """Do various validations and assign the channel name.

        If the channel name is None:
        1. Check if the channel already has a name. If so, do nothing.
        2. If not, generate one like this: _monitor_event or _event

        If the channel name is provided:
        1. If there is no name already assigned, use the given one.
        2. If there is and it matches, do nothing.
        3. If it does not match and it was automatically generated, switch
           to the given one.
        4. If it does not match and the existing one was not automatically
           generated, raise an exception.
        """
        if channel is None:
            # Channel not specified
            if self._channel is None:
                # No previous channel name. Need to generate one.
                if self._source_mon is None:
                    self._channel = "_{}".format(self._source_event)
                    self._sys.rename_connection(self, None)
                else:
                    self._channel = "_{}_{}".format(self._source_mon.name,
                            self._source_event)
                    self._source_mon.rename_connection(self, None)
        else:
            if self._channel is None:
                # No previous channel name. Use the given one.
                self._channel = channel
                if self._source_mon is None:
                    self._sys.rename_connection(self, None)
                else:
                    self._source_mon.rename_connection(self, None)
            elif self._channel == channel:
                # Given name matches what was already used.
                pass
            elif self._channel[0] == '_':
                # Given name doesn't match, but prior name was auto-generated.
                # Switch to the given name.
                old_channel = self._channel
                self._channel = channel
                if self._source_mon is None:
                    self._sys.rename_connection(self, old_channel)
                else:
                    self._source_mon.rename_connection(self, old_channel)
            else:
                # Previous name was not auto-generated and the provided name
                # does not match. Exception.
                if self._source_mon is None:
                    event_str = self._source_event
                else:
                    event_str = self._source_mon.name + '.' + self._source_event
                raise ChannelMismatch("Source event {} must always use the "
                        "same connection name".format(event_str))

    def add_target(self, target):
        """Add a Target to this channel after verifying that it is not a
        duplicate of any targets it already contains"""
        for t in self._targets:
            if target == t:
                raise DuplicateConnection("Source and destination of "
                        "connections cannot match.")
        self._targets.append(target)

class SynchronousSet(set):
    """A subclass of set customized to represent a Synchronous Set"""
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
            raise AlreadyInSyncset("Monitor {} cannot be added to a synchronous"
                    " set twice.".format(self.name))
        self._syncset = syncset

    def _validate_single_param(self, source_event, source_ev_params,
            param, type_, dest_name):
        """Validate type for a single parameter or state var against the
        monitor and event parameters in this source monitor.
        
        source_event - Name of the source event
        source_ev_params - List or tuple of source event parameter types
        params - Parameter object to validate
        type_ - SmedlType to validate against
        dest_name - Name of the thing being validated, e.g. "parameter ___ of
          event ___" or "state var ___ of monitor ___", to be used in exception
          messages
        """
        # Wildcard params always validate
        if param.index is None:
            return

        if param.identity:
            # Validate against monitor params
            try:
                result = self._params[param.index].convertible_to(type_)
            except IndexError:
                raise ParameterError("Source monitor {} does not have "
                        "identity {}".format(self._name, param))
            if not result:
                raise TypeMismatch("Param {} in source monitor {} "
                    "does not match dest {}".format(
                    param.index, self._name, dest_name))
        else:
            # Validate against event params
            try:
                result = source_ev_params[param.index].convertible_to(
                        type_)
            except IndexError:
                raise ParameterError("Source event {} does not have "
                        "identity {}".format(self._name, param))
            if not result:
                raise TypeMismatch("Param {} in source event {} "
                    "does not match dest {}".format(
                    param.index, source_event, dest_name))

    def _validate_param_types(self, source_event, source_ev_params,
            dest_params, dest_param_types, dest_name):
        """Validate types for a target parameter list against the monitor and
        event parameters in this source monitor.
        
        source_event - Name of the source event
        source_ev_params - List or tuple of source event parameter types
        dest_params - List or tuple of Parameter for the destination
        dest_param_types - List or tuple of destination parameter types
        dest_name - "monitor ___" or "event ___", to be used in exception
          messages
        """
        for i in range(len(dest_params)):
            param = dest_params[i]
            type_ = dest_param_types[i]

            self._validate_single_param(source_event, source_ev_params, param,
                    type_, "param {} in {}".format(i, dest_name))

    def add_connection(self, channel, source_event, target):
        """Add the given target to the proper connection for the source event
        (creating the connection if it does not exist yet).

        channel - Channel name, or None to use the default (the name used in
          another connection for this source event, or autogenerated if none)
        source_event - Name of the source event
        target - A Target object
        
        Raise a TypeMismatch if the target paramter types (or state var types
        for creation) do not match the source parameter types.
        
        Raise a ParameterError if there is some other issue with target
        parameters.

        Raise a ChannelMismatch if the channel name does not match what was
        previously used for this source event.
        
        Raise a DuplicateConnection if this connection matches one that already
        exists (same source and destination, ignoring parameters)."""
        # Check that source event exists and get the params
        try:
            source_ev_params = self._spec.exported_events[source_event]
        except KeyError:
            raise NameNotDefined("Source monitor {} does not contain exported "
                    "event {}".format(self._name, source_event))

        # Validate destination monitor parameter types. (Count must be validated
        # already.)
        self._validate_param_types(source_event, source_ev_params,
                target.mon_params, target.monitor.params,
                "monitor " + target.monitor.name)

        # Validate additional parameters depending on Target type
        if isinstance(target, TargetEvent):
            # Validate destination event parameter types
            dest_ev_types = target.monitor.spec.imported_events[
                    target.event_params]
            self._validate_param_types(source_event, source_ev_params,
                    target.event_params, dest_ev_types,
                    "event " + target.event)
        elif isinstance(target, TargetCreation):
            # Validate state var types
            for var, param in target.state_vars.items():
                var_type = target.monitor.spec.state_vars[var].type
            self._validate_single_param(source_event, source_ev_params,
                    param, var_type, "state var {} of monitor {}".format(
                    var, target.monitor.name))

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

    def rename_connection(self, conn, old_channel):
        """Put the given connection in the _connections dict under the correct
        name. Called by Connection when it is assigned an automatic or explicit
        name."""
        if old_channel is not None:
            del self._connections[old_channel]
        self._connections[conn.channel] = conn

    def create_export_connections(self):
        """Exported events that are not explicitly the source of a connection
        in the architecture specification implicitly get exported back to the
        environment. This creates those implicit TargetExports."""
        for event in self._spec.exported_events.keys():
            if event not in self._ev_connections:
                conn = Connection(self._sys, self, event)
                self._ev_connections[event] = conn
                conn.assign_name(None)
                conn.add_target(TargetExport())

    @property
    def intra_connections(self):
        """Return a list of connections where this monitor is the source and
        at least one destination is in the same synchronous set"""
        result = []
        for conn in self._connections.values():
            for target in conn.targets:
                if target.monitor in self._syncset:
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
                if target.monitor not in self._syncset:
                    result.append(conn)
                    break
        return result

    def __repr__(self):
        return "monitor {}({}) as {}".format(
                self._spec.name,
                ", ".join(self._params),
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

    @property
    def name(self):
        return self._name

    @name.setter
    def name(self, value):
        if self._name is None:
            self._name = value
        else:
            raise Exception("Internal error: Monitoring system already named")

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

    def add_syncset(self, name, monitors):
        """Add a synchronous set to the system.

        Parameters:
        name - Name of the synchronous set
        monitors - An iterable of monitor names to be added to the synchronous
          set. Monitors must already be declared and must not already be in a
          synchronous set.
        """
        # Ensure the synchronous set does not already exist
        if name in self._syncsets:
            raise NameCollision("Synchronous set {} is already defined".format(
                name))

        # Create the SynchronousSet
        syncset = SynchronousSet(name)

        # Iterate through the monitors, check if they exist, check if they are
        # already in a synchronous set, and assign them to the new synchronous
        # set
        for monitor in monitors:
            try:
                self._monitor_decls[monitor].assign_syncset(syncset)
            except KeyError:
                raise NameNotDefined("Monitor {} has not been declared".format(
                    monitor))
            syncset.add(monitor)

        # Add the syncset to the MonitorSystem
        self._syncsets[name] = syncset

    def _unused_syncset(self, monitor_name):
        """Find an unused synchronous set name for the named monitor. If the
        monitor name iself is not already a synchronous set, use that.
        Otherwise, append a number."""
        syncset = monitor_name
        i = 1
        while syncset in self._syncsets:
            i += 1
            syncset = monitor_name + str(i)
        if syncset != monitor_name:
            print("Warning: {} is already the name of a synchronous set. "
                    "Monitor {} will be in synchronous set {}".format(
                    monitor_name, syncset))
        return syncset

    def _validate_no_identities(self, params, dest_name):
        """Raise a ParameterError if any of the Parameters are identity
        parameters.

        params - An iterable of Parameter
        dest_name - A string to use in the exception, e.g. "Monitor ___" or
          "Event ___"
        """
        for param in params:
            if param.index is None:
                continue
            if param.identity:
                raise ParameterError('{} cannot use identity parameters '
                        '("Id."/"#") when there is no source monitor'
                        .format(dest_name))

    def add_connection(self, channel, monitor, source_event, target):
        """Add the given target to the proper connection for the source event
        (creating the connection if it does not exist yet).

        channel - Channel name, or None to use the default (the name used in
          another connection for this source event, or autogenerated if none)
        monitor - Declared monitor name, or None if from the target system
        source_event - Name of the source event
        target - A Target object
        
        Raise a TypeMismatch if the target paramter types (or state var types
        for creation) do not match the source parameter types.
        
        Raise a ParameterError if there is some other issue with target
        parameters.

        Raise a ChannelMismatch if the channel name does not match what was
        previously used for this source event.
        
        Raise a DuplicateConnection if this connection matches one that already
        exists (same source and destination, ignoring parameters)."""
        # If from a monitor, call that monitor's add_connection
        if monitor is not None:
            try:
                decl = self._monitor_decls[monitor]
            except KeyError:
                raise NameNotDefined("Source monitor {} is not declared"
                        .format(monitor))
            decl.add_connection(channel, source_event, target)
            return

        # Validate that the destination monitor parameters are all wildcards
        # or event parameters ("$x"), not monitor parameters ("#x")
        self._validate_no_identities(target.mon_params,
                "Monitor " + target.monitor.name)

        # Same for additional parameters, depending on target type
        if isinstance(target, TargetEvent):
            self._validate_no_identities(target.event_params,
                    "Event " + target.event)
        elif isinstance(target, TargetCreation):
            self._validate_no_identities(target.state_vars.values(),
                    "Monitor " + target.monitor.name)

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

    def rename_connection(self, conn, old_channel):
        """Put the given connection in the _imported_connections dict under the
        correct name. Called by Connection when it is assigned an automatic or
        explicit name."""
        if old_channel is not None:
            del self._imported_connections[old_channel]
        self._imported_connections[conn.channel] = conn

    def add_monitor_decl(self, name, target, params):
        """Add a monitor declaration to the system.

        Parameters:
        name - Name given to the monitor (i.e. the "as" name, if provided, or
          the regular name if not)
        target - a MonitorSpec for an imported monitor this name was assigned to
        params - A list of SmedlType representing the parameters (identities) of
          this monitor
        """
        # Check if the given name is already taken
        if name in self.monitor_decls:
            raise NameCollision("Monitor name {} is already declared".format(
                name))

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
                self.add_syncset(syncset, (mon,))

    def create_export_connections(self):
        """Iterate through all the monitor declarations and create export
        targets for all the exported events that are not already the source of
        an explicit connection."""
        for mon in self._monitor_decls.values():
            mon.create_export_connections()

    def imported_channels(self, syncset):
        """Get a list of Connections with sources not in the given synchronous
        set and destinations in it
        
        syncset - Name of the synchronous set"""
        result = []

        # Sort through the channels from the target system
        for conn in self._imported_connections.values():
            for target in conn.targets:
                if target.monitor in self._syncsets[syncset]:
                    result.append(conn)
                    break

        # Sort through channels from monitors
        for decl in self._monitor_decls.values():
            if decl not in self._syncsets[syncset]:
                for conn in decl.connections.values():
                    for target in conn.targets:
                        if target.monitor in self._syncsets[syncset]:
                            result.append(conn)
                            break

        return result

    def syncset_spec_names(self, syncset):
        """Get a set of the MonitorSpec names for the named syncset

        syncset - Name of the synchronous set"""
        result = set()
        for decl in self._syncsets[syncset]:
            result.add(decl.spec.name)
        return result
