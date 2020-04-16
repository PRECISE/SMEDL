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
    def __init__(self, out_dir=None, transport=None):
        """Initialize the MonitorGenerator with the selected options"""
        # Keep track of if we are generating a transport adapter so we can warn
        # when generating just a monitor (which does not include the transport
        # adapter)
        self.gen_transport = (transport is not None)

        # Initialize the actual code generator
        if out_dir is None:
            out_dir = '.'
        self.generator = codegen.CodeGenerator(out_dir, transport)

    def generate(self, input_file):
        """Generate code for a given input file"""
        # Determine whether input is an architecture file
        ext = os.path.splitext(input_file)[1].lower()
        if ext == '.smedl':
            if self.gen_transport:
                print("Warning: -t/--transport option only has an effect when "
                        "an architecture file is\ngiven", file=sys.stderr)

            # Parse a single monitor
            with open(input_file, "r") as f:
                input_text = f.read()
            parser = smedl_parser.SMEDLParser()
            monitor = parser.parse(input_text, rule_name='start',
                    semantics=smedl_semantics.SmedlSemantics())
            
            # Generate the code
            generator.write_one(monitor)
        else:
            # Parse an architecture file, which will also parse all monitors it
            # imports
            with open(input_file, "r") as f:
                input_text = f.read()
            parser = a4smedl_parser.A4SMEDLParser()
            system = parser.parse(input_text, rule_name='start',
                    semantics=a4smedl_semantics.A4smedlSemantics())
            
            # Generate the code
            generator.write_all(system)

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
    parser.add_argument('-t', '--transport', choices=["rabbitmq"],
            help="Generate an adapter for the given asynchronous transport "
            "method")
    #parser.add_argument('-t', '--thread-safe', help="Include code to enable "
    #        "thread safety (such as mutexes)", action='store_true')
    args = parser.parse_args()

    return (args.input,
        {
            'out_dir': args.dir,
            'transport': args.transport,
            #'mutexes': args.thread_safe,
        })

def main():
    input_file, options = parse_args()
    generator = MonitorGenerator(**options)
    generator.generate(input_file)

if __name__ == '__main__':
    main()
