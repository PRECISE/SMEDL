"""
Architecture file semantic actions
"""
from structures import arch
from . import common_semantics, smedl_parser, smedl_semantics
from .exceptions import (NameCollision, NameNotDefined, ParameterError,
        ChannelMismatch, TypeMismatch, DuplicateConnection)

class A4smedlSemantics(common_semantics.CommonSemantics):
    """Semantic actions for A4SMEDL parsing"""

    def __init__(self):
        # Initialize an empty system specification
        self.system = arch.MonitorSystem()

        # Monitor specifications from .smedl files. Key is name from file. Value
        # is parsed monitor.
        self.monitor_specs = dict()

        # Maintain records of which channel names are associated with which
        # source events and which source events are associated with which
        # channel names. Source events are either strings (for events imported
        # from the target system) or 2-tuples (monitor, event). This allows
        # verification that the same channel name and source event are always
        # paired in a connection.
        # See _connection_name_validations()
        self.channel_events = dict()
        self.event_channels = dict()

    def start(self, ast):
        """Return the monitor system"""
        self.system.assign_singleton_syncsets()
        return self.system

    def import_stmt(self, ast):
        """Parse the named SMEDL file and store the spec for use in monitor
        declarations"""
        # Strip the opening and closing quotes
        filename = ast[1:-1]

        # Read and parse the monitor from the named file
        with open(filename, "r") as f:
            smedl_spec = f.read()
        parser = smedl_parser.SMEDLParser()
        monitor_spec = parser.parse(smedl_spec, rule_name='start',
                semantics=smedl_semantics.SmedlSemantics())

        # Make sure monitor name is not already taken
        if monitor_spec.name in self.monitor_specs:
            raise NameCollision("Monitor named {} has already been imported"
                    .format(monitor_spec.name))

        self.monitor_specs[monitor_spec.name] = monitor_spec
        return ast

    def monitor_decl(self, ast):
        """Add a monitor declaration to the system"""
        # Make sure monitor has been imported
        if ast.name not in self.monitor_specs:
            raise NameNotDefined("Monitor {} has not been imported".format(
                ast.name))

        # If an "as" name was not given, use the actual name
        if ast.renamed is None:
            ast.renamed = ast.name

        self.system.add_monitor_decl(ast.renamed, self.monitor_specs[ast.name],
                self.params)

    def syncset_decl(self, ast):
        """Add a synchronous set to the system"""
        self.system.add_syncset(ast.name, ast.monitors)

    def _connection_name_validations(self, name, event):
        """Do various validations on channel names and their source event.

        name - A string representing the channel name, or None if not provided.
        event - A 2-tuple (monitor name, event name) representing the source
          event. If the event is sourced from the target system, monitor name
          must be None.

        If the channel name is not provided:
        1. Check if one already is assigned for this source event. If so, use
           that.
        2. If not, generate one like this: _monitor_event or _event

        If the channel name is provided:
        1. If there is no name already assigned, use the given one.
        2. If there is and it matches, use the given one.
        3. If it does not match and it was automatically generated, use the
           given one and convert all existing uses to the new channel name.
        4. If it does not match and the existing one was not automatically
           generated, raise an exception.

        Return the channel name to be used, whether the given one, a saved one,
        or a newly generated one.
        """
        if name is None:
            try:
                # Try previously assigned name
                return self.event_channels[event]

            except KeyError:
                # No previous name, use generated name
                if event[0] is None:
                    auto_name = "_{}".format(event[1])
                else:
                    auto_name = "_{}_{}".format(event[0], event[1])
                self.event_channels[event] = auto_name
                self.channel_events[auto_name] = event
                return auto_name

        else:
            try:
                saved_name = self.event_channels[event]
            except KeyError:
                # No previous name, use given name
                self.event_channels[event] = name
                self.channel_events[name] = event
                return name

            if saved_name == name:
                # Previous name matches, use given name
                return name

            elif saved_name[0] == '_'
                # Previous name was auto-generated
                # Convert all previous uses of the generated name to given name
                if (event[0] is None and saved_name in
                        self.system.imported_connections):
                    self.system.imported_connections[name] = (
                            self.system.imported_connections[saved_name])
                    del self.system.imported_connections[saved_name]
                elif (event[0] is not None and saved_name in
                        self.system.monitor_decls[event[0]].connections):
                    self.system.monitor_decls[event[0]].connections[name] = (
                            self.system.monitor_decls[event[0]].connections[
                            saved_name])
                    del self.system.monitor_decls[event[0]].connections[
                            saved_name]
                # Use the given name
                self.event_channels[event] = name
                del self.channel_events[saved_name]
                self.channel_events[name] = event
                return name

            else:
                # Previous name was not auto-generated and does not match the
                # given name. Error.
                event_str = event[1] if event[0] is None else '.'.join(event)
                raise ChannelMismatch("Source event {} must always use the same"
                        " connection name".format(event_str))

    def _validate_single_type(self, source_mon_params, source_ev_params,
            param, dest_type):
        """Validate a single destination param against the source parameters.
        Return True if valid, "#" if it is an invalid identity parameter, "$"
        if it is an invalid event parameter.

        source_mon_params - A list of SmedlType representing the parameters
          (identities) of the source monitor
        source_ev_params - A list of SmedlType representing the parameters
          of the source event
        param - A Parameter to validate
        dest_type - The SmedlType to validate against
        """
        # Wildcard param inherently valid
        if param.index is None:
            return True

        if param.identity:
            # Validate against monitor params
            if not source_mon_params[param.index].convertible_to(dest_type):
                return "#"
        else:
            # Validate against event params
            if not source_ev_params[param.index].convertible_to(dest_type):
                return "$"

    def _validate_param_types(self, source_mon_params, source_ev_params,
            dest_params, dest_types, dest_name):
        """Validate source param types against the list of Parameters
        
        source_mon_params - A list of SmedlType representing the parameters
          (identities) of the source monitor
        source_ev_params - A list of SmedlType representing the parameters
          of the source event
        dest_params - A list of Parameter represeting the parameters for either
          the destination monitor or event
        dest_types - A list of SmedlType representing the target types for the
          dest_params
        dest_name - "monitor ___" or "event ___", to be used in the TypeMismatch
          message
          
        Returns if all parameters are valid, or raises a TypeMismatch if not."""
        for i in range(len(dest_params)):
            param = ast.target.mon_params[i]
            # Wildcard param inherently valid
            result = self._validate_single_type(source_mon_params,
                    source_ev_params, param, dest_types[i])

            if result == "#":
                raise TypeMismatch("Param {} of source monitor does not match "
                        "param {} of {}".format(param.index, i, dest_name))
            if result == "$":
                raise TypeMismatch("Param {} of source event does not match "
                        "param {} of {}".format(param.index, i, dest_name))

    def connection_defn(self, ast):
        """Do various validations and add the connection to the system"""
        if ast.source.monitor is not None:
            # Check that source monitor exists and get source monitor params
            try:
                source_mon_params = self.system.monitor_decls[
                        ast.source.monitor].params
            except KeyError:
                raise NameNotDefined("Source monitor {} is not declared"
                        .format(ast.source.monitor))
            source_mon_decl = self.system.monitor_decls[ast.source.monitor]

            # Check that souce event exists and get source event params
            try:
                source_event_params = source_mon_decl.specs.exported_events[
                        ast.source.event]
            except KeyError:
                raise NameNotDefined("Source monitor {} does not contain "
                        "exported event {}".format(ast.source.monitor,
                        ast.source.event))

            # Validations on channel name
            ast.name = self._connection_name_validations(ast.name,
                    (ast.source.monitor, ast.source.event))
            # Assign channel name to Target object
            ast.target.set_channel(ast.name)

            # Validate destination monitor parameter types. Count is already
            # validated.
            target_mon_decl = self.system.monitor_decls[ast.target.monitor]
            self._validate_param_types(source_mon_params, source_event_params,
                    ast.target.mon_params, target_mon_decl.params, "monitor " +
                    target_mon_decl.name)

            if isinstance(ast.target, arch.TargetEvent):
                # Validate destination event parameter types
                target_ev = ast.target.event
                target_ev_types = target_mon_decl.specs.imported_events[
                        target_ev]
                self._validate_param_types(source_mon_params,
                        source_event_params, ast.target.event_params,
                        target_ev_types, "event " + target_ev)

            elif isinstance(ast.target, arch.TargetCreation)
                # Validate state vars
                for var, param in ast.target.state_vars.items():
                    # Validate that state var exists and get type
                    try:
                        dest_type = target_mon_decl.specs.state_vars[var]
                    except KeyError:
                        raise NameNotDefined("Monitor {} has no state variable "
                                "{}".format(target_mon_decl.name, var))
                    # Validate the type
                    result = self._validate_single_type(source_mon_params,
                            source_event_params, param, dest_type)
                    if result == "#":
                        raise TypeMismatch("Param {} of source monitor does not"
                                " match state var {} in {}".format(param.index,
                                var, target_mon_decl.name))
                    if result == "$":
                        raise TypeMismatch("Param {} of source event does not"
                                " match state var {} in {}".format(param.index,
                                var, target_mon_decl.name))

            # Make sure this is not a duplicate connection
            #TODO do we actually want this check?
            try:
                for target in source_mon_decl.connections[ast.source.event]:
                    if ast.target.same_as(target):
                        raise DuplicateConnection("Duplicate connections. "
                                "Source and destination of connections cannot "
                                "match.")
            except KeyError:
                pass

            # Add the connection to the source monitor
            try:
                source_mon_decl.connections[ast.source.event].append(ast.target)
            except KeyError:
                source_mon_decl.connections[ast.source.event] = [ast.target]

        else:
            # This is an event from the target system. There is much less we
            # can validate.

            # Validations on channel name
            ast.name = self._connection_name_validations(ast.name,
                    (None, ast.source.event))
            # Assign channel name to Target object
            ast.target.set_channel(ast.name)

            # Validate that destination monitor parameters are all wildcards
            # or event parameters ("$"), not monitor parameters ("#")
            for param in ast.target.mon_params:
                if param.index is None:
                    continue
                if param.identity:
                    raise ParameterError('Monitor {} cannot use identity '
                            'parameters ("Id."/"#") when there is no source '
                            'monitor'.format(ast.target.monitor))

            if isinstance(ast.target, arch.TargetEvent):
                # Validate destination event parameters are only from the source
                # event, not the source monitor
                for param in ast.target.event_params:
                    if param.identity:
                        raise ParameterError('Event {} cannot use identity '
                                'parameters ("Id."/"#") when there is no source'
                                ' monitor'.format(ast.target.event))

            elif isinstance(ast.target, arch.TargetCreation)
                # Validate state vars
                for var, param in ast.target.state_vars.items():
                    # Validate that state var exists
                    if var not in target_mon_decl.specs.state_vars:
                        raise NameNotDefined("Monitor {} has no state variable "
                                "{}".format(target_mon_decl.name, var))
                    # Validate that state var comes from event parameter, not
                    # source monitor parameter
                    if param.identity:
                        raise ParameterError('State var {} cannot use identity '
                                'parameters ("Id."/"#") when there is no source'
                                ' monitor'.format(var))

            # Make sure this is not a duplicate connection
            #TODO do we actually want this check?
            try:
                for target in self.system.imported_connections[ast.name]:
                    if ast.target.same_as(target):
                        raise DuplicateConnection("Duplicate connections. "
                                "Source and destination of connections cannot "
                                "match.")
            except KeyError:
                pass

            # Add the connection to the source monitor
            try:
                self.system.imported_connections[ast.name].append(ast.target)
            except KeyError:
                self.system.imported_connections[ast.name] = [ast.target]

    def target_event(self, ast):
        """Create a TargetEvent. Ensure the target monitor and event exist and
        have the correct number of parameters. Other checks are done by
        connection_defn."""
        # Check that destination monitor exists
        if ast.dest_monitor not in self.system.monitor_decls:
            raise NameNotDefined("Destination monitor {} is not declared"
                    .format(ast.dest_monitor))
        # Check that destination event exists as an imported event
        elif ast.dest_event not in self.system.monitor_decls[
                ast.dest_monitor].specs.imported_events:
            raise NameNotDefined("Destination monitor {} does not contain "
                    "imported event {}".format(ast.dest_event))

        # If monitor_params and/or event_params were not present, add them as
        # empty lists
        if ast.monitor_params is None:
            ast.monitor_params = []
        if ast.event_params is None:
            ast.event_params = []

        # Check that number of monitor params matches
        if len(ast.monitor_params) != len(self.system.monitor_decls[
                ast.dest_monitor].params):
            raise ParameterError("Expected {} parameters (identities) for "
                    "montor {}, got {}".format(len(self.system.monitor_decls[
                    ast.dest_monitor].params), ast.dest_monitor,
                    len(ast.monitor_params)))
        # Check that the number of event params matches
        if len(ast.event_params) != len(self.system.monitor_decls[
                ast.dest_monitor].specs.imported_events[ast.dest_event]):
            raise ParameterError("Expected {} parameters for event {}.{}, "
                    "got {}".format(len(self.system.monitor_decls[
                    ast.dest_monitor].specs.imported_events[ast.dest_event]),
                    ast.dest_monitor, ast.dest_event, len(ast.monitor_params)))

        # Create the TargetEvent
        return arch.TargetEvent(self.dest_monitor, self.dest_event,
                self.monitor_params, self.event_params)

    def monitor_initialization(self, ast):
        """Create a TargetCreation. Ensure the target monitor exists and has the
        correct number of parameters."""
        # Check that destination monitor exists
        if ast.dest_monitor not in self.system.monitor_decls:
            raise NameNotDefined("Destination monitor {} is not declared"
                    .format(ast.dest_monitor))

        # Make sure we are not creating a monitor with no parameters. Such
        # monitors are initialized once at global wrapper startup and cannot
        # have separate instances.
        if len(self.system.monitor_decls[ast.dest_monitor].params) == 0:
            raise ParameterError("Monitor {} without parameters cannot "
                    "receive new instances".format(ast.dest_monitor))

        # Make sure the number of monitor parameters matches. Don't need to
        # ensure there are no wildcard parameters because the grammar will not
        # allow it.
        if ast.monitor_params is None or len(ast.monitor_params) != len(
                self.system.monitor_decls[ast.dest_monitor].params):
            raise ParameterError("Expected {} parameters (identities) for "
                    "montor {}, got {}".format(len(self.system.monitor_decls[
                    ast.dest_monitor].params), ast.dest_monitor,
                    (0 if ast.monitor_params is None else
                        len(ast.monitor_params))))

        # Create a dict for state variable initialization
        state_vars = dict()
        for initializer in ast.state_vars:
            state_vars[initializer.var_name] = initializer.value

        # Create the TargetCreation
        return arch.TargetCreation(ast.dest_monitor, ast.monitor_params,
                state_vars)

    def wildcard_parameter(self, ast):
        """Create a Parameter that might be a wildcard"""
        if isinstance(ast, arch.Parameter):
            return ast
        elif ast.kind == '*':
            return arch.Parameter(True, None)
        else:
            # This should not happen. It means there is a mistake in the grammar
            raise ValueError("Internal error: Invalid parameter source")

    def parameter(self, ast):
        """Create a Parameter"""
        if ast.kind == '#':
            return arch.Parameter(True, ast.index)
        elif ast.kind == '$':
            return arch.Parameter(False, ast.index)
        else:
            # This should not happen. It means there is a mistake in the grammar
            raise ValueError("Internal error: Invalid parameter source")
