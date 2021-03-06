# Copyright (c) 2021 The Trustees of the University of Pennsylvania
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""
Architecture file semantic actions
"""
import os.path

from smedl.structures import arch
from . import common_semantics, smedl_parser, smedl_semantics
from .exceptions import NameCollision, NameNotDefined, ParameterError


class A4smedlSemantics(common_semantics.CommonSemantics):
    """Semantic actions for A4SMEDL parsing"""

    def __init__(self, path, transport=None):
        # Store the path which imported monitors will be relative to
        self.path = path

        # Initialize an empty system specification
        self.system = arch.MonitorSystem(default_transport=transport)

        # Monitor specifications from .smedl files. Key is name from file.
        # Value is parsed monitor.
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
        self.system.complete_system()
        return self.system

    def declaration(self, ast):
        """Set the monitor system name"""
        self.system.name = ast
        return ast

    def import_stmt(self, ast):
        """Parse the named SMEDL file and store the spec for use in monitor
        declarations"""
        # Strip the opening and closing quotes and join with the path
        filename = os.path.join(self.path, ast[1:-1])
        dirname = os.path.dirname(filename)

        # Read and parse the monitor from the named file
        with open(filename, "r") as f:
            smedl_spec = f.read()
        parser = smedl_parser.SMEDLParser()
        monitor_spec = parser.parse(
            smedl_spec, rule_name='start',
            semantics=smedl_semantics.SmedlSemantics(dirname))

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
        renamed = ast.name if ast.renamed is None else ast.renamed

        self.system.add_monitor_decl(
            renamed, self.monitor_specs[ast.name], ast.params)
        return ast

    def event_decl(self, ast):
        """Add an event declaration from the target system to the monitor
        system"""
        if ast.kind == 'exported':
            self.system.add_exported_event(ast.name, ast.params)
        else:
            self.system.add_connection(ast.name, ast.params)
        return ast

    def syncset_decl(self, ast):
        """Add a synchronous set to the system"""
        self.system.add_syncset(ast.name, ast.members)
        return ast

    def connection_defn(self, ast):
        """Do various validations and add the connection to the system"""
        if ast.source.monitor == 'pedl':
            del ast.source['monitor']
        self.system.add_target(
            ast.name, ast.source.monitor, ast.source.event, ast.target)
        return ast

    def target_event(self, ast):
        """Create a TargetEvent. Ensure the target monitor and event exist and
        have the correct number of parameters. Other checks are done by
        connection_defn."""
        # Check if this is actually a PEDL event, in which case TargetExport
        # should be created
        if ast.dest_monitor == 'pedl':
            if ast.monitor_params is not None:
                raise ParameterError("'pedl' event {} cannot have monitor "
                                     "identities".format(ast.dest_event))
            ast['name'] = ast.dest_event
            ast['params'] = ast.event_params
            return self._exported_event(ast)

        # Check that destination monitor exists
        if ast.dest_monitor not in self.system.monitor_decls:
            raise NameNotDefined("Destination monitor {} is not declared"
                                 .format(ast.dest_monitor))
        # Check that destination event exists as an imported event
        elif ast.dest_event not in self.system.monitor_decls[
                ast.dest_monitor].spec.imported_events:
            raise NameNotDefined(
                "Destination monitor {} does not contain imported event {}"
                .format(ast.dest_monitor, ast.dest_event))

        # If monitor_params and/or event_params were not present, add them as
        # empty lists
        if ast.monitor_params is None:
            ast['monitor_params'] = []
        if ast.event_params is None:
            ast['event_params'] = []

        # Check that number of monitor params matches
        if len(ast.monitor_params) != len(self.system.monitor_decls[
                ast.dest_monitor].params):
            raise ParameterError(
                "Expected {} parameters (identities) for montor {}, got {}"
                .format(len(self.system.monitor_decls[
                    ast.dest_monitor].params), ast.dest_monitor,
                    len(ast.monitor_params)))
        # Check that the number of event params matches
        if len(ast.event_params) != len(self.system.monitor_decls[
                ast.dest_monitor].spec.imported_events[ast.dest_event]):
            raise ParameterError(
                "Expected {} parameters for event {}.{}, got {}"
                .format(len(self.system.monitor_decls[
                    ast.dest_monitor].spec.imported_events[ast.dest_event]),
                    ast.dest_monitor, ast.dest_event, len(ast.event_params)))

        # Create the TargetEvent
        return arch.TargetEvent(
                self.system.monitor_decls[ast.dest_monitor], ast.dest_event,
                ast.monitor_params, ast.event_params)

    def _monitor_initialization(self, ast):
        """Create a TargetCreation. Ensure the target monitor exists and has the
        correct number of parameters."""
        # Check that destination monitor exists
        if ast.name not in self.system.monitor_decls:
            raise NameNotDefined("Destination monitor {} is not declared"
                                 .format(ast.name))

        # Make sure we are not creating a monitor with no parameters. Such
        # monitors are initialized once at global wrapper startup and cannot
        # have separate instances.
        if len(self.system.monitor_decls[ast.name].params) == 0:
            raise ParameterError(
                "Monitor {} without parameters cannot receive new instances"
                .format(ast.name))

        # Make sure the number of monitor parameters matches. Don't need to
        # ensure there are no wildcard parameters because the grammar will not
        # allow it.
        if len(ast.params[0]) != len(
                self.system.monitor_decls[ast.name].params):
            raise ParameterError(
                "Expected {} parameters (identities) for montor {}, got {}"
                .format(len(self.system.monitor_decls[ast.name].params),
                        ast.name, len(ast.params[0])))

        # Create a dict for state variable initialization and check that state
        # vars all exist
        state_vars = dict()
        for initializer in ast.params[1]:
            if (initializer.var_name not in
                    self.system.monitor_decls[ast.name].spec.state_vars):
                raise NameNotDefined("Monitor {} has no state var {}".format(
                    ast.name, initializer.var_name))
            state_vars[initializer.var_name] = initializer.value

        # Create the TargetCreation
        return arch.TargetCreation(
            self.system.monitor_decls[ast.name], ast.params[0], state_vars)

    def _exported_event(self, ast):
        """Create a TargetExport."""
        try:
            exported_event = self.system.exported_events[ast.name]
        except KeyError:
            exported_event = self.system.add_exported_event(ast.name)
        else:
            # Check number of params for existing exported event.
            # (Types are checked when the target is added to a connection.)
            if exported_event.params is not None and (
                    len(ast.params[0]) != len(exported_event.params)):
                raise ParameterError("Expected {} parameters for PEDL event "
                                     "{}, got {}.".format(
                                         len(exported_event.params), ast.name,
                                         len(ast.params[0])))
        return arch.TargetExport(exported_event, ast.params[0])

    def exported_event_or_monitor_initialization(self, ast):
        """Determine based on the name whether this is an exported event or
        monitor initialization and call the appropriate semantics function."""
        if ast.name in self.system.monitor_decls:
            return self._monitor_initialization(ast)
        else:
            if ast.params[1] != []:
                # If there are any state var initializations in the parameter
                # list, the intention must be a monitor creation, not exporting
                # a PEDL event.
                raise NameNotDefined("Destination monitor {} is not "
                                     "declared".format(ast.name))
            return self._exported_event(ast)

    def initialization_parameter_list(self, ast):
        """Transform AST into (list of parameters, list of initializers)"""
        if ast.first is None:
            return ([], ast.initializers)
        if ast.rest is None:
            return ([ast.first], [])
        params, initializers = ast.rest
        params.insert(0, ast.first)
        return (params, initializers)

    def wildcard_parameter(self, ast):
        """Create a Parameter that might be a wildcard"""
        if isinstance(ast, arch.Parameter):
            return ast
        elif ast.kind == '*':
            return arch.Parameter(True, None)
        else:
            # This should not happen. It means there's a mistake in the grammar
            raise ValueError("Internal error: Invalid parameter source")

    def parameter(self, ast):
        """Create a Parameter"""
        if ast.kind == '#':
            return arch.Parameter(True, int(ast.index))
        elif ast.kind == '$':
            return arch.Parameter(False, int(ast.index))
        else:
            # This should not happen. It means there's a mistake in the grammar
            raise ValueError("Internal error: Invalid parameter source")
