"""
Code generation and template filling
"""

import os.path

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

    def write_static_files(self):
        """Write the static code to the output directory"""
        from . import static
        files = resources.contents(static)
        for f in files:
            if f == '__init__.py':
                continue
            elif resources.is_resource(static, f):
                outpath = os.path.join(self.dest_dir, f)
                text = resources.read_text(static, f)
                with open(outpath, "w") as outfile:
                    f.write(text)

    def write_wrappers(self, system, syncset_name):
        """Write the global wrapper and local wrappers for one synchronous set

        Parameters:
        system - A MonitorSystem containing the synchronous set
        syncset_name - The name of the synchronous set whose wrappers should be
          generated
        """

    def write_monitor(self, monitor_spec, syncset_name):
        """Write the files for one monitor specification

        Parameters:
        monitor_spec - A MonitorSpec whose monitor should be written
        syncset_name - The name of the synchronous set to which this monitor
          belongs
        """
        pass #TODO

    def write_all(self, system):
        """Write all C files for the provided monitoring system

        Parameters:
        system - A MonitorSystem for which code should be generated
        """
        self.write_static_files()

        pass #TODO
