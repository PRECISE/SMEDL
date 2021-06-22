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
Monitor Generator

Generate code for monitors from SMEDL and architecture specifications
"""

import sys
import os.path
import argparse

from smedl import __about__
from smedl.parser import (smedl_parser, smedl_semantics, a4smedl_parser,
                          a4smedl_semantics)
from smedl import codegen


class MonitorGenerator(object):
    """Coordinate parsing and template filling"""
    def __init__(
            self, out_dir=None, transport=None, makefile=True, helpers=True,
            overwrite=False):
        """Initialize the MonitorGenerator with the selected options

        out_dir - A string or path-like object for the directory where the
          generated files are to be placed, or None for the current directory
        transport - The name of the transport mechanism to generate (e.g.
          'rabbitmq', 'ros')
        makefile - Whether or not to generate a Makefile for monitor systems.
          True=yes (if an architecture file and transport are given), False=no,
        overwrite - Whether files that may contain customizations (Makefiles,
          various ROS files, RabbitMQ config) should be overwritten
        helpers - Whether or not to copy helper headers to the out_dir (helpers
          are never copied if out_dir is the same directory they already
          reside in)
        """
        # Keep track of if we are generating a transport adapter so we can warn
        # when generating just a monitor (which does not include the transport
        # adapter)
        self.gen_transport = (transport is not None)
        self.transport = transport

        # Initialize the actual code generator
        if out_dir is None:
            out_dir = '.'
        self.generator = codegen.construct_generator(
            transport=transport,
            dest_dir=out_dir,
            makefile=makefile,
            overwrite=overwrite,
            helpers=helpers)

    def generate(self, input_file):
        """Generate code for a given input file (which may be a string or a
        path-like object)"""
        # Determine whether input is an architecture file
        ext = os.path.splitext(input_file)[1].lower()
        dirname = os.path.dirname(input_file)
        if ext == '.smedl':
            if self.gen_transport:
                print("Warning: -t/--transport option only has an effect when "
                      "an architecture file is\ngiven", file=sys.stderr)

            # Parse a single monitor
            with open(input_file, "r") as f:
                input_text = f.read()
            parser = smedl_parser.SMEDLParser()
            self.monitor = parser.parse(
                input_text, rule_name='start',
                semantics=smedl_semantics.SmedlSemantics(dirname))

            # Generate the code
            self.generator.write_one(self.monitor)
        else:
            # Parse an architecture file, which will also parse all monitors it
            # imports
            if not self.gen_transport:
                print("Notice: No -t/--transport option was chosen. "
                      "Generating a monitor system\nwithout transport code.",
                      file=sys.stderr)
            with open(input_file, "r") as f:
                input_text = f.read()
            parser = a4smedl_parser.A4SMEDLParser()
            self.system = parser.parse(
                input_text, rule_name='start',
                semantics=a4smedl_semantics.A4smedlSemantics(dirname,
                                                             self.transport))

            # Generate the code
            self.generator.write_all(self.system)


def parse_args():
    """Handle argument parsing. Return arguments as a tuple (input, options)
    where input is the input file name and options is a dict of options ready
    to pass to the MonitorGenerator constructor"""
    parser = argparse.ArgumentParser(
        description="Monitor Generator for SMEDL monitoring systems")

    parser.add_argument(
        '--version', action='version', version=__about__['version'])
    parser.add_argument(
        'input', help='The input file. If the extension is ".smedl", a single '
        'monitor is generated. Otherwise, input is assumed to be an '
        'architecture file and a full monitoring system is generated.')
    parser.add_argument(
        '-d', '--dir', help="Directory to write the generated code to (if not "
        "current directory)")
    parser.add_argument(
        '-t', '--transport', choices=['rabbitmq', 'ros'],
        help="Generate an adapter for the given asynchronous transport "
        "method. This option is usually recommended when the input is an "
        "architecture file. A Makefile will be generated (except with 'ros', "
        "which uses its own build system). If the input is a .smedl file, "
        "this option has no effect.")
    m_group = parser.add_mutually_exclusive_group()
    m_group.add_argument(
        '-f', '--force-overwrite', action='store_true',
        help="Certain files are meant to be customizable after generation "
        "(Makefiles; RabbitMQ cfg; ROS CMakeLists.txt, package.xml, and "
        "*_ros_config.inc). Normally, these are not overwritten if they are "
        "already present to preserve any such customizations. This option "
        "forces ALL files to be overwritten, including these.")
    m_group.add_argument(
        '--no-makefile', action='store_false', dest='makefile',
        help="Never generate a Makefile")
    parser.add_argument(
        '-n', '--no-copy-helpers', action='store_false', dest='helpers',
        help="Do not copy helper headers (helper headers are never copied if "
        "the destination is the same directory they already reside in)")
    # parser.add_argument('-t', '--thread-safe', help="Include code to enable "
    #        "thread safety (such as mutexes)", action='store_true')
    args = parser.parse_args()

    return (
        args.input,
        {
            'out_dir': args.dir,
            'transport': args.transport,
            'makefile': args.makefile,
            'helpers': args.helpers,
            'overwrite': args.force_overwrite
        })


def main():
    input_file, options = parse_args()
    generator = MonitorGenerator(**options)
    generator.generate(input_file)


if __name__ == '__main__':
    main()
