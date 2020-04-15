"""
Code generation and template filling
"""

import os.path
import jinja2
from smedl.structures import expr

# importlib.resources is only available in python>=3.7, but is available as a
# backport.
try:
    from importlib import resources
except ImportError:
    import importlib_resources as resources

class CodeGenerator(object):
    """Generates C code for monitors and monitor systems"""
    def __init__(self, dest_dir, transport):
        """Initialize the code generator.

        Parameters:
        dest_dir - Directory to write to
        transport - Name of the asynchronous transport mechanism
        """
        self.dest_dir = dest_dir
        self.transport = transport

        # Initialize the Jinja2 environment
        self.env = jinja2.Environment(trim_blocks=True, lstrip_blocks=True,
                keep_trailing_newline=True,
                loader=jinja2.PackageLoader('smedl.codegen', '.'),
                globals={'SmedlType': expr.SmedlType})

        # Set up some custom tests for convenience in templates
        self.env.tests['nonempty'] = lambda x: len(x) > 0

    def _write_static_files(self):
        """Write the static code to the output directory"""
        from . import static
        files = resources.contents(static)
        for f in files:
            if f == '__init__.py':
                continue
            elif resources.is_resource(static, f):
                out_path = os.path.join(self.dest_dir, f)
                text = resources.read_text(static, f)
                with open(out_path, "w") as outfile:
                    f.write(text)

    def _render(self, template, filename, values):
        """Render the named template to the named file in the output directory
        using the given key-value store.

        Parameters:
        template - Name of the template to use
        filename - Name of the generated file
        values - A dict containing the key-value store to pass to the template
        """
        out_path = os.path.join(self.dest_dir, filename)
        text = self.env.get_template(template).render(values)
        with open(out_path, "w") as f:
            f.write(text)

    def _write_rabbitmq(self, system, syncset_name):
        """Write the RabbitMQ adapter"""
        pass #TODO

    def _write_wrappers(self, system, syncset_name):
        """Write the global wrapper and local wrappers for one synchronous set

        Parameters:
        system - A MonitorSystem containing the synchronous set
        syncset_name - The name of the synchronous set whose wrappers should be
          generated
        """
        # Write the local wrappers
        for mon_name in system.syncsets[syncset_name]:
            values = {
                    "mon": system.monitor_decls[mon_name],
                    "spec": system.monitor_decls[mon_name].spec,
                }
            self._render("local_wrapper.c", mon_name + "_local_wrapper.c",
                    values)
            self._render("local_wrapper.h", mon_name + "_local_wrapper.h",
                    values)

        # Write the global wrapper
        values = {
                "sys": system,
                "syncset": syncset_name,
                "mon_decls": [system.monitor_decls[mon] for mon in
                        system.syncsets[syncset_name]]
            }
        self._render("global_wrapper.c", syncset_name + "_global_wrapper.c",
                values)
        self._render("global_wrapper.h", syncset_name + "_global_wrapper.h",
                values)

        # Write the transport adapter, if requested
        if self.transport == "rabbitmq":
            self._write_rabbitmq(system, syncset_name)
        elif self.transport == "ros":
            pass #TODO

    def _write_monitor(self, monitor_spec):
        """Write the files for one monitor specification

        Parameters:
        monitor_spec - A MonitorSpec whose monitor should be written
        """
        # Generate the template vars
        values = {
                "spec": monitor_spec,
            }

        # Write the files
        self._render("mon.c", monitor_spec.name + "_mon.c", values)
        self._render("mon.h", monitor_spec.name + "_mon.h", values)

    def write_one(self, monitor):
        """Write all C files for the single monitor described by the provided
        specification

        Parameters:
        monitor - The MonitorSpec whose code should be generated
        """
        self._write_static_files()
        self._write_monitor(monitor)

    def write_all(self, system):
        """Write all C files for the provided monitoring system

        Parameters:
        system - A MonitorSystem for which code should be generated
        """
        self._write_static_files()

        # Collect the monitor specs to generate
        mon_specs = dict()
        for decl in system.monitor_decls.values():
            if decl.spec.name not in mon_specs:
                mon_specs[decl.spec.name] = decl.spec

        # Generate monitors
        for spec in mon_specs.values():
            self._write_monitor(spec)

        # Generate wrappers
        for syncset_name in system.syncsets.keys():
            self._write_wrappers(system, syncset_name)
