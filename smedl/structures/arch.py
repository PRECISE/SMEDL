"""
Structures and types for monitoring system architectures (.a4smedl files)
"""

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
        self.identity = identity
        self.index = index

class Target(object):
    """The target of a connection, such as an imported event or monitor
    creation. Note that this is not the same as the "target system," which is
    the system being monitored."""
    def __init__(self, type_, monitor, mon_params):
        """Initialize the Target object.
        
        type_ - String describing the type of target for Jinja
        monintor - Name of the destination monitor
        mon_params - List of Parameters for the monitor identities"""
        self.target_type = type_
        self.monitor = monitor
        self.mon_params = mon_params

    def set_channel(self, channel):
        """Set the connection (a.k.a channel) name. This is how events are
        identified when they are sourced from outside a synchronous set (e.g.
        from another synchronous set or from the target system). The message
        encapsulating the event will typicall have a name within the body as
        well, but that is mainly for human reference. It is not used by the
        tool."""
        self.channel = channel

    def same_as(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        return self.monitor == other.monitor

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
        self.event = dest_event
        self.event_params = event_params

    def same_as(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        if not isinstance(other, TargetEvent):
            return False
        return super().same_as(other) and self.event == other.event

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
        self.state_vars = state_vars

    def same_as(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        if not isinstance(other, TargetCreation):
            return False
        return super().same_as(other)

class TargetExport(Target):
    """An event export target, for events that are exported out of a synchronous
    set back to the target system. Note that "export target" and "target system"
    are two different senses of the word "target," the former being a connection
    target and the latter being the target of monitoring."""
    def __init__(self):
        """Initialize this export target."""
        super().__init__('export', None, [])

class DeclaredMonitor(object):
    """A monitor delcaration from the architecture file"""
    def __init__(self, name, spec, params):
        # Name of the monitor given in the declaration (meaning the "as" name,
        # if provided)
        self.name = name
        # The monitor.MonitorSpec to use for this monitor
        self.spec = spec
        # List of the parameter types to use for this monitor (as SmedlTypes)
        self.params = params
        # Name of the synchronous set this monitor belongs to
        self.syncset = None
        # Connections that originate from this monitor. Keys are source event
        # names. Values are lists of Target.
        self.connections = dict()

    def assign_syncset(self, syncset):
        """Assign the monitor to a synchronous set. If it is already in one,
        raise AlreadyInSyncset"""
        if self.syncset is not None:
            raise AlreadyInSyncset("Monitor {} cannot be added to a synchronous"
                    " set twice.".format(self.name))
        self.syncset = syncset

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

    def has_intra_events(self, syncset):
        """Check if the monitor has any connections that are destined within the
        synchronous set and return True or False

        syncset - List of monitor names in the synchronous set
        """
        for target_list in self.connections.values():
            for target in target_list:
                if target.monitor in syncset:
                    return True
        return False

    def has_inter_events(self, syncset):
        """Check if the monitor has any connections that are destined outside
        the synchronous set and return True or False

        syncset - List of monitor names in the synchronous set
        """
        for target_list in self.connections.values():
            for target in target_list:
                if target.monitor not in syncset:
                    return True
        return False

    def __repr__(self):
        return "monitor {}({}) as {}".format(
                self.spec,
                ", ".join(self.params),
                self.name)+eagfedj0omme0

class MonitorSystem(object):
    """A monitor system as specified by an architecture file (a4smedl file)"""
    def __init__(self):
        # Monitor declarations. Keys are the "as X" names of the monitors,
        # values are DeclaredMonitors
        self.monitor_decls = dict()

        # Synchronous sets. Keys are names of synchronous sets. Values are sets
        # of monitor names.
        self.syncsets = dict()

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
        self.imported_connections = dict()

    def assign_name(self, name):
        """Assign a name to the monitoring system"""
        self.name = name

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

    def add_syncset(self, name, monitors):
        """Add a synchronous set to the system.

        Parameters:
        name - Name of the synchronous set
        monitors - A list of monitor names to be added to the synchronous set.
          Monitors must already be declared and must not already be in a
          synchronous set.
        """
        # Ensure the synchronous set does not already exist
        if name in self.syncsets:
            raise NameCollision("Synchronous set {} is already defined".format(
                name))

        # Iterate through the monitors, check if they exist, check if they are
        # already in a synchronous set, and assign them to the new synchronous
        # set
        for monitor in monitors:
            try:
                self.monitor_decls[monitor].assign_syncset(name)
            except KeyError:
                raise NameNotDefined("Monitor {} has not been declared".format(
                    monitor))

        # Add the syncset to the MonitorSystem
        self.syncsets[name] = set(monitors)

    def _unused_syncset(self, monitor_name):
        """Find an unused synchronous set name for the named monitor. If the
        monitor name iself is not already a synchronous set, use that.
        Otherwise, append a number."""
        syncset = monitor_name
        i = 1
        while syncset in self.syncsets:
            i += 1
            syncset = monitor_name + str(i)
        if syncset != monitor_name:
            print("Warning: {} is already the name of a synchronous set. "
                    "Monitor {} will be in synchronous set {}".format(
                    monitor_name, syncset))
        return syncset

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
