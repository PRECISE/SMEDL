"""
Code generation and template filling
"""

import os.path
import jinja2

# importlib.resources is only available in python>=3.7, but is available as a
# backport.
try:
    from importlib import resources
except ModuleNotFoundError:
    import importlib_resources as resources

class CodeGenerator(object):
    """Generates C code for monitors and monitor systems"""
    def __init__(self, dest_dir):
        """Initialize the code generator.

        Parameters:
        dest_dir - Directory to write to
        """
        if dest_dir is None:
            self.dest_dir = '.'
        else:
            self.dest_dir = dest_dir

        # Initialize the Jinja2 environment
        self.env = jinja2.Environment(trim_blocks=True, lstrip_blocks=True,
                keep_trailing_newline=True,
                loader=jinja2.PackageLoader('smedl.codegen', '.'))

        # Set up some custom tests for convenience in templates
        self.env.tests.['nonempty'] = lambda x: len(x) > 0

    def write_static_files(self):
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

    def write_wrappers(self, system, syncset_name):
        """Write the global wrapper and local wrappers for one synchronous set

        Parameters:
        system - A MonitorSystem containing the synchronous set
        syncset_name - The name of the synchronous set whose wrappers should be
          generated
        """
        pass #TODO

    def write_monitor(self, monitor_spec):
        """Write the files for one monitor specification

        Parameters:
        monitor_spec - A MonitorSpec whose monitor should be written
        """
        # Generate the template vars
        values = {
                "spec": monitor_spec,
            }

        # Write the files
        self.render("mon.c", monitor_spec.name + "_mon.c", values)
        self.render("mon.h", monitor_spec.name + "_mon.h", values)

    def write_all(self, system):
        """Write all C files for the provided monitoring system

        Parameters:
        system - A MonitorSystem for which code should be generated
        """
        self.write_static_files()

        pass #TODO
