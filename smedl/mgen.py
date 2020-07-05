#!/usr/bin/env python3

"""
Monitor Generator

Generate code for monitors from SMEDL and architecture specifications
"""

import sys
import os.path
import argparse
from smedl import __about__
from smedl.parser import (smedl_parser, smedl_semantics,
        a4smedl_parser, a4smedl_semantics)
from smedl import codegen

class MonitorGenerator(object):
    """Coordinate parsing and template filling"""
    def __init__(self, out_dir=None, transport=None, makefile=None,
            helpers=True):
        """Initialize the MonitorGenerator with the selected options

        out_dir - A string or path-like object for the directory where the
          generated files are to be placed, or None for the current directory
        transport - The name of the transport mechanism to generate (e.g.
          'rabbitmq', 'ros', 'file')
        makefile - Whether or not to generate a Makefile for monitor systems.
          True=yes (if an architecture file and transport are given), False=no,
          None=only if not already present in the destination
        helpers - Whether or not to copy helper headers to the out_dir (helpers
          are never copied if out_dir is the same directory they already
          reside in)
        """
        # Keep track of if we are generating a transport adapter so we can warn
        # when generating just a monitor (which does not include the transport
        # adapter)
        self.gen_transport = (transport is not None)

        # Initialize the actual code generator
        if out_dir is None:
            out_dir = '.'
        self.generator = codegen.CodeGenerator(out_dir, transport, makefile,
                helpers)

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
            self.monitor = parser.parse(input_text, rule_name='start',
                    semantics=smedl_semantics.SmedlSemantics(dirname))
            
            # Generate the code
            self.generator.write_one(self.monitor)
        else:
            # Parse an architecture file, which will also parse all monitors it
            # imports
            with open(input_file, "r") as f:
                input_text = f.read()
            parser = a4smedl_parser.A4SMEDLParser()
            self.system = parser.parse(input_text, rule_name='start',
                    semantics=a4smedl_semantics.A4smedlSemantics(dirname))
            
            # Generate the code
            self.generator.write_all(self.system)

def parse_args():
    """Handle argument parsing. Return arguments as a tuple (input, options)
    where input is the input file name and options is a dict of options ready
    to pass to the MonitorGenerator constructor"""
    parser = argparse.ArgumentParser(description="Monitor Generator for SMEDL "
            "monitoring systems")

    #TODO Add some of these back in later?
    #parser.add_argument('-s', '--structs', help='Print internal data '
    #        'structures', action='store_true')
    #parser.add_argument('--noimplicit', help='Disable implicit error handling '
    #        'in generated monitor', action='store_false')



    parser.add_argument('--version', action='version',
            version=__about__['version'])
    parser.add_argument('input', help='The input file. If the extension is '
            '".smedl", a single monitor is generated. Otherwise, input is '
            'assumed to be an architecture file and a full monitoring system is'
            ' generated.')
    parser.add_argument('-d', '--dir', help="Directory to write the generated "
            "code to (if not current directory)")
    #TODO Add ROS as a wrapper
    parser.add_argument('-t', '--transport', choices=['rabbitmq', 'file'],
            help="Generate an adapter for the given asynchronous transport "
            "method")
    m_group = parser.add_mutually_exclusive_group()
    m_group.add_argument('-m', '--makefile', action='store_const', const=True,
            help="Generate a Makefile even if it would overwrite one already "
            "present in the destination directory (Makefiles are never "
            "generated if an .a4smedl file is not provided or no "
            "-t/--transport option is given)")
    m_group.add_argument('--no-makefile', action='store_const', const=False,
            default=argparse.SUPPRESS, dest='makefile',
            help="Never generate a Makefile")
    parser.add_argument('-n', '--no-copy-helpers', action='store_false',
            help="Do not copy helper headers (helper headers are never copied "
            "if the destination is the same directory they already reside in)",
            dest='helpers')
    #parser.add_argument('-t', '--thread-safe', help="Include code to enable "
    #        "thread safety (such as mutexes)", action='store_true')
    args = parser.parse_args()

    return (args.input,
        {
            'out_dir': args.dir,
            'transport': args.transport,
            'makefile': args.makefile,
            'helpers': args.helpers,
            #'mutexes': args.thread_safe,
        })

def main():
    input_file, options = parse_args()
    generator = MonitorGenerator(**options)
    generator.generate(input_file)

if __name__ == '__main__':
    main()
