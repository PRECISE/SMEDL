#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function, division, absolute_import, unicode_literals
from .smedl_parser import smedlParser

class smedlSymbolTable(object):
    def __init__(self):
        return









class smedlSemantics(object):
    def object(self, ast):
        return ast

    def variable_declaration(self, ast):
        return ast

    def event_definition(self, ast):
        return ast

    def scenario_definition(self, ast):
        return ast

    def trace_definition(self, ast):
        return ast

    def step_definition(self, ast):
        return ast

    def event_instance(self, ast):
        return ast

    def action(self, ast):
        return ast

    def action_item(self, ast):
        return ast

    def state_update(self, ast):
        return ast

    def raise_stmt(self, ast):
        return ast

    def instantiation_stmt(self, ast):
        return ast

    def type(self, ast):
        return ast

    def identifier(self, ast):
        return ast

    def integer(self, ast):
        return ast

    def float(self, ast):
        return ast

    def expression(self, ast):
        return ast

    def and_expr(self, ast):
        return ast

    def comp_expr(self, ast):
        return ast

    def arith_expr(self, ast):
        return ast

    def term(self, ast):
        return ast

    def factor(self, ast):
        return ast

    def atom(self, ast):
        return ast

    def trailer(self, ast):
        return ast

    def target(self, ast):
        return ast

    def parameter_list(self, ast):
        return ast

    def expression_list(self, ast):
        return ast

    def identifier_list(self, ast):
        return ast

    def state_update_list(self, ast):
        return ast

    def nonempty_action_item_list(self, ast):
        return ast


def main(filename, startrule, trace=False, whitespace=None):
    import json
    with open(filename) as f:
        text = f.read()
    parser = smedlParser(parseinfo=False)
    ast = parser.parse(
        text,
        startrule,
        filename=filename,
        trace=trace,
        whitespace=whitespace)
    print('AST:')
    print(ast)
    print()
    print('JSON:')
    print(json.dumps(ast, indent=2))
    print()

if __name__ == '__main__':
    import argparse
    import string
    import sys

    class ListRules(argparse.Action):
        def __call__(self, parser, namespace, values, option_string):
            print('Rules:')
            for r in smedlParser.rule_list():
                print(r)
            print()
            sys.exit(0)

    parser = argparse.ArgumentParser(description="Simple parser for smedl.")
    parser.add_argument('-l', '--list', action=ListRules, nargs=0,
                        help="list all rules and exit")
    parser.add_argument('-t', '--trace', action='store_true',
                        help="output trace information")
    parser.add_argument('-w', '--whitespace', type=str, default=string.whitespace,
                        help="whitespace specification")
    parser.add_argument('file', metavar="FILE", help="the input file to parse")
    parser.add_argument('startrule', metavar="STARTRULE",
                        help="the start rule for parsing")
    args = parser.parse_args()

    main(args.file, args.startrule, trace=args.trace, whitespace=args.whitespace)
