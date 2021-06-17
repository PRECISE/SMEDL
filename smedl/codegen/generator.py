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
Code generation and template filling
"""

import os
import os.path
import shutil
import itertools

import jinja2
from jinja2 import nodes
from jinja2 import ext
from jinja2.exceptions import TemplateRuntimeError

import smedl.structures.arch
from smedl.structures import expr
from smedl.parser.exceptions import SmedlException

# importlib.resources is only available in python>=3.7, but is available as a
# backport in earlier versions.
try:
    from importlib import resources
except ImportError:
    import importlib_resources as resources


class UnsupportedFeature(TemplateRuntimeError, SmedlException):
    """Raised when a particular feature of SMEDL is incompatible with the
    chosen generation options (e.g. a particular transport adapter)"""


class UnsupportedFeatureExtension(ext.Extension):
    """Jinja2 extension to create an "unsupported" tag that raises
    UnsupportedFeature. Use like this:

    {% unsupported "Some message here" %}
    """
    tags = set(['unsupported'])

    def _raise_unsupported(self, msg, caller):
        raise UnsupportedFeature(msg)

    def parse(self, parser):
        lineno = next(parser.stream).lineno
        # Parse the argument (the message)
        args = [parser.parse_expression()]
        # Return an ExprStmt (evals an expression and discards it) where the
        # expression is a call to _raise_unsupported
        return nodes.ExprStmt(
                self.call_method('_raise_unsupported', args, lineno=lineno),
                lineno=lineno)


def construct_generator(transport, **kwargs):
    """Construct a CodeGenerator or one of its subclasses for the appropriate
    transport type.

    transport - Name of the asynchronous transport mechanism

    Other arguments are passed through to the CodeGenerator (or subclass)
    constructor.
    """
    generators = {
        None: CodeGenerator,
        'rabbitmq': RabbitMQGenerator,
        'ros': ROSGenerator,
        'file': FileGenerator,
    }

    return generators[transport](**kwargs)


class CodeGenerator(object):
    """Generates C code for monitors and monitor systems"""
    def __init__(self, dest_dir, makefile, overwrite, helpers):
        """Initialize the code generator.

        Parameters:
        dest_dir - Directory to write to
        makefile - Whether a Makefile should be written with write_all.
          True=yes (if a transport was given), False=no
        overwrite - Whether customizable files (Makefile, certain ROS files,
          RabbitMQ config) should be overwritten
        helpers - Whether or not to copy helper headers to the out_dir (helpers
          are never copied if out_dir is the same directory they already
          reside in)
        """
        self.dest_dir = dest_dir
        self.helpers = helpers
        self.overwrite = overwrite

        # Subclasses should set to True if there is C++ code present
        self.cpp = False

        # Most subclasses will use makefile generation, but vanilla
        # CodeGenerator can't (because we don't have a complete program without
        # a transport adapter).
        if type(self) is CodeGenerator:
            self.makefile = False
        else:
            self.makefile = makefile

        # Initialize the Jinja2 environment
        self.env = jinja2.Environment(
            trim_blocks=True,
            lstrip_blocks=True,
            keep_trailing_newline=True,
            undefined=jinja2.StrictUndefined,
            extensions=[UnsupportedFeatureExtension],
            loader=jinja2.ChoiceLoader(self._get_jinja_loaders()))

        # Make SmedlType available to all templates
        self.env.globals['SmedlType'] = expr.SmedlType
        self.env.globals['chain'] = itertools.chain

        # Set up some custom tests for convenience in templates
        self.env.tests['nonempty'] = lambda x: len(x) > 0

    def _get_jinja_loaders(self):
        """Return a list of Jinja template loaders to use. Subclasses should
        override to extend the list."""
        return [jinja2.PackageLoader('smedl.codegen', '.')]

    def _append_paths(self, orig, to_add, dirname):
        """Extend the list of paths

        orig - The list to extend
        to_add - A list of paths to extend with
        dirname - A directory to join each path in to_add with

        Each path in to_add is only added if it's not a file already in orig
        """
        for fname in to_add:
            path = os.path.join(dirname, fname)
            append = True
            for existing in orig:
                try:
                    if os.path.samefile(existing, path):
                        append = False
                except OSError:
                    append = False
            if append:
                orig.append(path)

    def _write_static_files(self, module):
        """Write the static code to the output directory. Must be provided with
        a module that contains nothing but the static resources and __init__.py
        """
        files = resources.contents(module)
        for f in files:
            if f == '__init__.py':
                continue
            elif resources.is_resource(module, f):
                out_path = os.path.join(self.dest_dir, f)
                text = resources.read_text(module, f)
                with open(out_path, "w") as outfile:
                    outfile.write(text)

    def _render(self, template, filename, values, dest=None, preserve=False):
        """Render the named template to the named file in the output directory
        using the given key-value store.

        Parameters:
        template - Name of the template to use
        filename - Name of the generated file
        values - A dict containing the key-value store to pass to the template
        dest - Directory to write to, defaulting to self.dest_dir
        preserve - If True, don't overwrite files that already exist unless
          self.overwrite is True
        """
        if dest is None:
            dest = self.dest_dir
        out_path = os.path.join(dest, filename)
        if preserve and not self.overwrite and os.path.exists(out_path):
            return
        text = self.env.get_template(template).render(values)
        with open(out_path, "w") as f:
            f.write(text)

    def _copy_files(self, files=[]):
        """Copy the list of files to the destination directory, if the
        destination directory isn't the same as where each file is being copied
        from. Skip any files that don't exist or cannot be copied."""
        for f in files:
            src_dir = os.path.dirname(f)
            try:
                if not os.path.samefile(src_dir, self.dest_dir):
                    shutil.copy(f, self.dest_dir)
            except OSError:
                pass

    def _write_makefile(self, system):
        """Write the Makefile

        Parameters:
        system - A MonitorSystem whose Makefile is to be written
        """
        syncset_mons = dict()
        for syncset in system.syncsets.values():
            syncset_mons[syncset.name] = [
                decl.name for decl in syncset
                if isinstance(decl, smedl.structures.arch.DeclaredMonitor)]

        syncset_specs = dict()
        for syncset in system.syncsets.values():
            specs = []
            for decl in syncset:
                if not isinstance(decl, smedl.structures.arch.DeclaredMonitor):
                    continue
                if decl.spec.name not in specs:
                    specs.append(decl.spec.name)
            syncset_specs[syncset.name] = specs

        pedl_syncsets = []
        for name, syncset in system.syncsets.items():
            if not syncset.pure_async:
                pedl_syncsets.append(name)

        values = {
            "transport": self.transport,
            "system": system.name,
            "syncsets": system.syncsets.keys(),
            "pedl_syncsets": pedl_syncsets,
            "syncset_mons": syncset_mons,
            "syncset_specs": syncset_specs,
            "mon_names": system.monitor_decls.keys(),
            "spec_names": [decl.spec.name for decl in
                           system.monitor_decls.values()]
        }
        self._render("Makefile", "Makefile", values, preserve=True)

    def _write_systemwide(self, system):
        """Write the files used for the entire monitoring system

        Paremeters:
        system - The MonitorSystem to generate for
        """
        values = {
            "sys": system,
        }
        self._render("defs.h", system.name + "_defs.h", values)

        # Generate Makefile, if requested
        if self.makefile:
            self._write_makefile(system)

    def _write_wrappers(self, system, syncset):
        """Write the global wrapper and local wrappers for one synchronous set

        Parameters:
        system - A MonitorSystem containing the synchronous set
        syncset - The synchronous set whose wrappers should be generated
        """
        # Write the local wrappers
        for mon in system.syncsets[syncset.name]:
            if not isinstance(mon, smedl.structures.arch.DeclaredMonitor):
                continue
            values = {
                "mon": mon,
                "spec": mon.spec,
            }
            self._render("local_wrapper.c", mon.name + "_local_wrapper.c",
                         values)
            self._render("local_wrapper.h", mon.name + "_local_wrapper.h",
                         values)

        # Write the global wrapper and manager
        mon_decls = [mon for mon in system.syncsets[syncset.name]
                     if isinstance(mon, smedl.structures.arch.DeclaredMonitor)]
        values = {
            "sys": system,
            "syncset": syncset.name,
            "pure_async": syncset.pure_async,
            "cpp": self.cpp,
            "mon_decls": mon_decls,
        }
        self._render("global_wrapper.c", syncset.name + "_global_wrapper.c",
                     values)
        self._render("global_wrapper.h", syncset.name + "_global_wrapper.h",
                     values)
        self._render("manager.c", syncset.name + "_manager.c", values)
        self._render("manager.h", syncset.name + "_manager.h", values)

        # Write the PEDL stub for synchronous sets with PEDL events
        if not syncset.pure_async:
            self._render("stub.c", syncset.name + "_stub.c", values)
            self._render("stub.h", syncset.name + "_stub.h", values)

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

    def _get_helpers(self, monitor):
        """Get a list of helper headers from the monitor that are #included
        with quotes and no subdirectories"""
        result = []
        for helper in monitor.helpers:
            if helper[0] != '"':
                continue
            if os.path.dirname(helper[1:-1]) == "":
                result.append(helper[1:-1])
        return result

    def _write_transport_adapters(self, system):
        """Subclasses should override this to generate the transport adapter
        code."""
        pass

    def write_one(self, monitor):
        """Write all C files for the single monitor described by the provided
        specification

        Parameters:
        monitor - The MonitorSpec whose code should be generated
        """
        from . import static
        self._write_static_files(static)
        self._write_monitor(monitor)

        # Copy helpers that are in the same directory as the .smedl file
        if self.helpers:
            helpers = self._get_helpers(monitor)
            full_helpers = []
            self._append_paths(full_helpers, helpers, monitor.path)
            self._copy_files(full_helpers)

    def write_all(self, system):
        """Write all C files for the provided monitoring system

        Parameters:
        system - A MonitorSystem for which code should be generated
        """
        from . import static
        self._write_static_files(static)

        # Collect the monitor specs to generate
        mon_specs = dict()
        for decl in system.monitor_decls.values():
            if decl.spec.name not in mon_specs:
                mon_specs[decl.spec.name] = decl.spec

        # Generate monitors
        for spec in mon_specs.values():
            self._write_monitor(spec)

        # Generate wrappers
        for syncset in system.syncsets.values():
            self._write_wrappers(system, syncset)

        # Generate systemwide files
        self._write_systemwide(system)

        # Generate transport adapters
        self._write_transport_adapters(system)

        # Copy helpers that are in the same directory as the .smedl file
        if self.helpers:
            full_helpers = []
            for spec in mon_specs.values():
                helpers = self._get_helpers(spec)
                self._append_paths(full_helpers, helpers, spec.path)
            self._copy_files(full_helpers)


class RabbitMQGenerator(CodeGenerator):
    """Generates C code for monitor systems with the RabbitMQ adapter."""
    def __init__(self, **kwargs):
        """Initialize the code generator for RabbitMQ.
        Parameters match the constructor for CodeGenerator."""
        super(RabbitMQGenerator, self).__init__(**kwargs)

        # Used by Makefile template
        self.transport = "rabbitmq"

    def _get_jinja_loaders(self):
        """Return a list of Jinja template loaders to use."""
        loaders = super(RabbitMQGenerator, self)._get_jinja_loaders()
        loaders.append(jinja2.PackageLoader('smedl.codegen.rabbitmq', '.'))
        return loaders

    def _write_transport_adapters(self, system):
        """Write the RabbitMQ adapters"""
        # Write static code
        from .rabbitmq import static
        self._write_static_files(static)

        # Write RabbitMQ adapters
        for syncset in system.syncsets.values():
            mon_decls = [
                mon for mon in system.syncsets[syncset.name]
                if isinstance(mon, smedl.structures.arch.DeclaredMonitor)]
            values = {
                "sys": system,
                "syncset": syncset.name,
                "pure_async": syncset.pure_async,
                "mon_decls": mon_decls,
            }
            self._render("rabbitmq.c", syncset.name +
                         "_rabbitmq.c", values)
            self._render("rabbitmq.h", syncset.name + "_rabbitmq.h", values)
            self._render("rabbitmq.cfg", system.name + ".cfg",
                         values, preserve=True)


#TODO File adapter isn't really compatible with the manager design. Once it is
# possible to put all PEDL events in a synchronous set, there is little reason
# to use it, anyway. (It was essentially a synchronous transport for
# asynchronous events.) Remove it at that point.
class FileGenerator(CodeGenerator):
    """Generates C code for monitor systems with the File adapter."""
    def __init__(self, **kwargs):
        """Initialize the code generator for the file transport.
        Parameters match the constructor for CodeGenerator."""
        super(FileGenerator, self).__init__(**kwargs)

        # Used by Makefile template
        self.transport = "file"

    def _get_jinja_loaders(self):
        """Return a list of Jinja template loaders to use."""
        loaders = super(FileGenerator, self)._get_jinja_loaders()
        loaders.append(jinja2.PackageLoader('smedl.codegen.file', '.'))
        return loaders

    def _write_transport_adapters(self, system):
        """Write the file adapters"""
        # Write static code
        from .file import static
        self._write_static_files(static)

        # Write file adapters
        for syncset_name in system.syncsets.keys():
            values = {
                "sys": system,
                "mon_decls": system.monitor_decls.values(),
                "syncsets": system.syncsets,
            }
            self._render("file.c", system.name + "_file.c", values)
            self._render("file.h", system.name + "_file.h", values)


class ROSGenerator(CodeGenerator):
    """Generates C code for monitor systems with the ROS adapter."""
    def __init__(self, **kwargs):
        """Initialize the code generator for ROS.
        Parameters match the constructor for CodeGenerator, except that a
        Makefile is never generated."""
        super(ROSGenerator, self).__init__(**kwargs)
        self.cpp = True

        # ROS uses catkin make, a customized version of CMake. Disable the
        # normal Makefile generation.
        self.makefile = False

    def _get_jinja_loaders(self):
        """Return a list of Jinja template loaders to use."""
        loaders = super(ROSGenerator, self)._get_jinja_loaders()
        loaders.append(jinja2.PackageLoader('smedl.codegen.ros', '.'))
        return loaders

    def _mkdir(self, *args):
        """Make the directory formed by joining all the arguments with the
        package directory with os.path.join. Parent directories must exist,
        but will not fail if the target directory already exists."""
        target = os.path.join(self.pkg_dir, *args)
        try:
            os.mkdir(target)
        except FileExistsError:
            pass

    def write_all(self, system):
        """Generate a ROS package for the provided monitoring system.

        Parameters:
        system - A MonitorSystem for which code should be generated
        """
        # ROSGenerator creates a full ROS package. This is the directory for
        # that package.
        self.pkg_dir = os.path.join(self.dest_dir, "smedl_" + system.name)

        # Generate the skeleton of the ROS package
        self._mkdir()
        self._mkdir('src')
        self._mkdir('msg')
        self._mkdir('launch')

        # Set the destination directory for monitor generation to the "src"
        # directory in the package
        self.dest_dir = os.path.join(self.pkg_dir, 'src')

        super(ROSGenerator, self).write_all(system)

    def _write_transport_adapters(self, system):
        """Write the code for the ROS package"""
        msg_dir = os.path.join(self.pkg_dir, 'msg')
        src_dir = os.path.join(self.pkg_dir, 'src')
        launch_dir = os.path.join(self.pkg_dir, 'launch')

        # Gather lists of inbound (from outside SMEDL), outbound (to outside
        # SMEDL), and internal (from and to only SMEDL) connections
        inbound_connections = system.imported_connections.values()
        internal_connections = []
        outbound_connections = []
        for decl in system.monitor_decls.values():
            for conn in decl.connections.values():
                if None in conn.inter_syncsets:
                    outbound_connections.append(conn)
                else:
                    internal_connections.append(conn)
        all_connections = (list(inbound_connections) + internal_connections +
                           outbound_connections)

        # Write message definitions for the various events that need to be
        # transported over ROS
        for conn in inbound_connections:
            values = {
                "sys": system,
                "params": conn.source_event_params,
                "ids": [],
            }
            self._render("event.msg", conn.channel + "Msg.msg",
                         values, msg_dir)
        for conn in internal_connections + outbound_connections:
            values = {
                "sys": system,
                "params": conn.source_event_params,
                "ids": conn.source_mon.params,
            }
            self._render("event.msg", conn.channel + "Msg.msg",
                         values, msg_dir)

        # Write launch file
        values = {
            "sys": system,
        }
        self._render("system.launch", system.name + ".launch",
                     values, launch_dir)

        # Write configuration include file
        values = {
            "sys": system,
            "inbound_connections": inbound_connections,
            "internal_connections": internal_connections,
            "outbound_connections": outbound_connections,
        }
        self._render("ros_config.inc", system.name + "_ros_config.inc",
                     values, src_dir, preserve=True)

        # Write package build configuration and metadata
        values = {
            "sys": system,
            "connections": all_connections,
        }
        self._render("CMakeLists.txt", "CMakeLists.txt",
                     values, self.pkg_dir, preserve=True)
        self._render("package.xml", "package.xml",
                     values, self.pkg_dir, preserve=True)

        # Write node sources
        for syncset in system.syncsets.values():
            mon_decls = [
                mon for mon in system.syncsets[syncset.name]
                if isinstance(mon, smedl.structures.arch.DeclaredMonitor)]
            values = {
                "sys": system,
                "syncset": syncset.name,
                "pure_async": syncset.pure_async,
                "mon_decls": mon_decls,
            }
            self._render("node.cpp", syncset.name + "_node.cpp", values)
            self._render("node.h", syncset.name + "_node.h", values)
            self._render("ros.h", syncset.name + "_ros.h", values)
