#!/usr/bin/env python

"""
Monitor Generator

Generate code for monitors from SMEDL and architecture specifications
"""

import os.path
import argparse
from smedl import __about__
from parser import (smedl_parser, smedl_semantics,
        a4smedl_parser, a4smedl_semantics)
import codegen

def generate(input_file, out_dir=None, rabbitmq=False, mutexes=False):
    """Coordinate parsing and template filling"""
    # Initialize the code generator
    generator = codegen.CodeGenerator(out_dir)

    # Determine whether an architecture file
    ext = os.path.splitext(input_file).lower()
    if ext == '.smedl':
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
    """Handle argument parsing and return relevant data in a dict ready to be
    passed to generate()"""
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
    #parser.add_argument('-r', '--rabbitmq', help="Generate the RabbitMQ wrapper"
    #        " for the global wrapper", action='store_true')
    #parser.add_argument('-t', '--thread-safe', help="Include code to enable "
    #        "thread safety (such as mutexes)", action='store_true')
    args = parser.parse_args()

    return {
            'input_file': args.input,
            'out_dir': args.dir,
            #'rabbitmq': args.rabbitmq,
            #'mutexes': args.thread_safe,
        }

def main():
    args = parse_args()
    generate(**args)

if __name__ == '__main__':
    main()
