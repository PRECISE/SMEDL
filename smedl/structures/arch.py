"""
Structures and types for monitoring system architectures (.a4smedl files)
"""

from parser.exceptions import NameCollision, NameNotDefined, AlreadyInSyncset

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
    def __init__(self, monitor, mon_params):
        """Initialize the Target object.
        
        monintor - Name of the destination monitor
        mon_params - List of Parameters for the monitor identities"""
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
        super().__init__(dest_monitor, mon_params)
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
        super().__init__(dest_monitor, mon_params)
        self.state_vars = state_vars

    def same_as(self, other):
        """Return True if the other is the same target (ignoring parameters)
        as ourselves"""
        if not isinstance(other, Target):
            return NotImplemented
        if not isinstance(other, TargetCreation):
            return False
        return super().same_as(other)

class DeclaredMonitor(object):
    """A monitor delcaration from the architecture file"""
    def __init__(self, name, specs, params):
        # Name of the monitor given in the declaration (meaning the "as" name,
        # if provided)
        self.name = name
        # The monitor.MonitorSpec to use for this monitor
        self.specs = specs
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

    def __repr__(self):
        return "monitor {}({}) as {}".format(
                self.specs,
                ", ".join(self.params),
                self.name)

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
