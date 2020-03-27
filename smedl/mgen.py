#!/usr/bin/env python

"""
Monitor Generator

Generate code for monitors from SMEDL and architecture specifications
"""

import argparse
from smedl import __about__
from parser import a4smedl_parser, a4smedl_semantics
import codegen

def generate(input_file, out_dir=None):
    """Coordinate parsing and template filling"""
    # Parse the architecture file (which will also parse any SMEDL files it
    # imports)
    with open(input_file, "r") as f:
        input_text = f.read()
    parser = a4smedl_parser.A4SMEDLParser()
    system = parser.parse(input_text, rule_name='start',
            semantics=a4smedl_semantics.A4smedlSemantics())

    # Generate the code
    generator = codegen.CodeGenerator(out_dir)
    generator.write_all(system)

def parse_args():
    """Handle argument parsing and return relevant data in a dict ready to be
    passed to generate()"""
    parser = argparse.ArgumentParser(description="Monitor Generator for SMEDL "
            "monitoring systems")

    #TODO Add some of these back in later?
    #parser.add_argument('-s', '--structs', help='Print internal data structures', action='store_true')
    #parser.add_argument('-d', '--debug', help='Show debug output', action='store_true')
    #parser.add_argument('-c', '--console', help='Only output to console, no file output', action='store_true')
    #parser.add_argument('--noimplicit', help='Disable implicit error handling in generated monitor', action='store_false')
    #parser.add_argument('-j', '--synchronous', help='Generate synchronous interface with no JSON handling', action='store_false')



    parser.add_argument('--version', action='version',
            version=__about__['version'])
    parser.add_argument('input', help="The architecture file to generate a "
            "monitor system from")
    #TODO: Detect if architecture file or smedl file from extension, maybe have
    # option to override
    parser.add_argument('--dir', help="Directory to write the generated code to"
            " (if not current directory)")
    args = parser.parse_args()

    return {
            'input_file': args.input,
            'out_dir': args.dir,
        }

def main():
    args = parse_args()
    generate(**args)

if __name__ == '__main__':
    main()
