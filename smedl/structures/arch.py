"""
Structures and types for monitoring system architectures (.a4smedl files)
"""

import types
from smedl.parser.exceptions import (NameCollision, NameNotDefined,
        AlreadyInSyncset)

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
        monintor - Name of the destination monitor
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

    def same_as(self, other):
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
        
        dest_monitor - Name of the destination monitor
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

    def same_as(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        if not isinstance(other, TargetEvent):
            return False
        return super().same_as(other) and self._event == other._event

    def __repr__(self):
        mon_param_str = ', '.join([str(p) for p in self._mon_params])
        ev_param_str = ', '.join([str(p) for p in self._event_params])
        return ('TargetEvent:' + self._monitor + '[' + mon_param_str + '].' +
                self._event + '(' + ev_param_str + ')')

class TargetCreation(Target):
    """A monitor creation target. Note that this is not the same as the "target
    system," which is the system being monitored."""
    def __init__(self, dest_monitor, mon_params, state_vars):
        """Initialize this target creation event.

        dest_monitor - Name of the monitor to be created
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

    def same_as(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        if not isinstance(other, TargetCreation):
            return False
        return super().same_as(other)

    def __repr__(self):
        mon_param_str = ', '.join([str(p) for p in self._mon_params])
        state_var_str = ', '.join([k + '=' + str(v)
                for k, v in self._state_vars.values()])
        return ('TargetCreation:' + self._monitor + '(' + mon_param_str +
                ', ' + state_var_str + ')')

class TargetExport(Target):
    """An event export target, for events that are exported out of a synchronous
    set back to the target system. Note that "export target" and "target system"
    are two different senses of the word "target," the former being a connection
    target and the latter being the target of monitoring."""
    def __init__(self):
        """Initialize this export target."""
        super().__init__('export', None, [])

    def same_as(self, other):
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

#TODO Incorporate this into DeclaredMonitors and MonitoringSystem.
#TODO Have a way to look up connections by name? Would that be useful? Or how
#  else do we need to look up connections?
#TODO Probably also useful to be able to have `intra_connections` and
#  `inter_connections` properties in a DeclaredMonitor
class Connection(object):
    """A connection between a source event and some number of targets"""
    def __init__(self, channel, source_mon=None):
        """Create a connection with the given channel name"""
        # The channel name
        self._channel = channel
        # The source DeclaredMonitor for this connection (or None if from the
        # target system)
        #TODO Either set this in constructor or add a setter
        self._source_mon = None
        # The source event name for this connection
        #TODO Either set this in constructor or add a setter
        self._source_event = None
        # A list of Targets that this connection links to
        # TODO Have a way to add to this
        self._targets = []

    @property
    def channel(self):
        return self._channel

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
    def __init__(self, name, spec, params):
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

    def assign_syncset(self, syncset):
        """Assign the monitor to a synchronous set. If it is already in one,
        raise AlreadyInSyncset"""
        if self._syncset is not None:
            raise AlreadyInSyncset("Monitor {} cannot be added to a synchronous"
                    " set twice.".format(self.name))
        self._syncset = syncset

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
        #TODO Do all the validations, create the Connection object if necessary
        # and add it to both dicts, then add the Target to that Connection
        # and set the Target's connection.
        pass #TODO

    #TODO Refactor below here

    def create_export_connections(self):
        """Exported events that are not explicitly the source of a connection
        in the architecture specification implicitly get exported back to the
        environment. This creates those implicit TargetExports."""
        for event in self.spec.exported_events.keys():
            if event not in self.connections:
                export_target = TargetExport()
                # Set channel name using the autogenerate format from
                # A4SmedlSemantics._connection_name_validations()
                export_target.set_channel("_{}_{}".format(self.name, event))
                self.connections[event] = [export_target]

    #TODO Needed after issue #29 is implemented?
    def is_event_intra(self, event, syncset):
        """Check if the named event has a connection that is destined within the
        synchronous set and return True or False

        event - Name of the event
        syncset - List of monitor names in the synchronous set
        """
        try:
            for target in self.connections[event]:
                if target.monitor in syncset:
                    return True
        except KeyError:
            return False
        return False

    #TODO Needed after issue #29 is implemented?
    def is_event_inter(self, event, syncset):
        """Check if the named event has a connection that is destined outside
        the synchronous set and return True or False

        event - Name of the event
        syncset - List of monitor names in the synchronous set
        """
        try:
            for target in self.connections[event]:
                if target.monitor not in syncset:
                    return True
        except KeyError:
            return False
        return False

    def intra_channels(self, syncset):
        """Return a list of channel names from this monitor that are destined
        to monitors inside the synchronous set

        syncset - List of monitor names in the synchronous set"""
        results = []
        for target_list in self.connections.values():
            for target in target_list:
                if target.monitor in syncset:
                    results.append(target.channel)
                    break
        return results

    def inter_channels(self, syncset):
        """Return a list of channel names from this monitor that are destined
        to monitors outside the synchronous set

        syncset - List of monitor names in the synchronous set"""
        results = []
        for target_list in self.connections.values():
            for target in target_list:
                if target.monitor not in syncset:
                    results.append(target.channel)
                    break
        return results

    def channels(self):
        """Return a set of channel names where this monitor is the source"""
        results = set()
        for target_list in self.connections.values():
            for target in target_list:
                results.add(target.channel)

    def __repr__(self):
        return "monitor {}({}) as {}".format(
                self.spec,
                ", ".join(self.params),
                self.name)+eagfedj0omme0

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

        # Monitor to monitor connections are in DeclaredMonitor.connections.
        #   This allows the code generator to organize nested switches with
        #   monitors in the outer switch and target events or creations on the
        #   inner switch.
        # Events imported from the target system are in this dict, where keys
        #   are channel names and values are lists of Target.
        # Note that events exported to the target system are identified by not
        #   having a Target for that event in its DeclaredMonitor, but we should
        #   consider having an explicit way to cause events to be exported in
        #   the architecture file. Such could become either a new subclass of
        #   Target or simply a TargetEvent with the destination monitor set to
        #   None.
        self._imported_connections = dict()

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

    def add_syncset(self, name, monitors):
        """Add a synchronous set to the system.

        Parameters:
        name - Name of the synchronous set
        monitors - A list of monitor names to be added to the synchronous set.
          Monitors must already be declared and must not already be in a
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
            syncset.add(self)

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

    #TODO Refactor below here

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
        self.monitor_decls[name] = DeclaredMonitor(name, target, params)

    def assign_singleton_syncsets(self):
        """Assign any monitors that are not already in a synchronous set to
        their own isolated synchronous sets. Normally, these synchronous sets
        will be named after the monitor, but if that name is already taken,
        a warning will be displayed and a number appended."""
        for mon in self.monitor_decls.values():
            if mon.syncset is None:
                syncset = self._unused_syncset(mon.name)
                mon.assign_syncset(syncset)
                self.syncsets[syncset] = {mon.name}
    
    def create_export_connections(self):
        """Iterate through all the monitor declarations and create export
        targets for all the exported events that are not already the source of
        an explicit connection."""
        for mon in self.monitor_decls.values():
            mon.create_export_connections()

    def get_syncset_spec_names(self, syncset):
        """Get a list of monitor specification names for all monitors in a
        synchronous set"""
        decls = [self.monitor_decls[mon] for mon in self.syncsets[syncset]]
        spec_names = set([decl.spec.name for decl in decls])
        return list(spec_names)

    def imported_channels(self, syncset):
        """Get all the channels imported to the given synchronous set as a dict
        where keys are the channel names and values are lists of target"""
        result = dict()

        # Sort through the channels from the target system
        for channel, targets in self.imported_connections.items():
            target_list = []
            for target in targets:
                if target.monitor in self.syncsets[syncset]:
                    target_list.append(target)
            if len(target_list) > 0:
                result[channel] = target_list

        # Sort through channels from monitors
        for decl in self.monitor_decls.values():
            if decl.name in self.syncsets[syncset]:
                continue
            for targets in decl.connections.values():
                target_list = []
                for target in targets:
                    if target.monitor in self.syncsets[syncset]:
                        target_list.append(target)
                if len(target_list) > 0:
                    result[target_list[0].channel] = target_list

        return result
