#!/usr/bin/env python
# -*- coding: utf-8 -*-

# CAVEAT UTILITOR
#
# This file was automatically generated by Grako.
#
#    https://pypi.python.org/pypi/grako/
#
# Any changes you make to it will be overwritten the next time
# the file is generated.


from __future__ import print_function, division, absolute_import, unicode_literals
from grako.parsing import graken, Parser


__version__ = (2015, 8, 7, 15, 30, 38, 4)

__all__ = [
    'pedlParser',
    'pedlSemantics',
    'main'
]


class pedlParser(Parser):
    def __init__(self, whitespace=None, nameguard=True, **kwargs):
        super(pedlParser, self).__init__(
            whitespace=whitespace,
            nameguard=nameguard,
            **kwargs
        )

    @graken()
    def _object_(self):
        self._token('object')
        self._identifier_()
        self.ast['object'] = self.last_node
        self._token('events')

        def block2():
            self._new_mon_()
        self._positive_closure(block2)

        self.ast['monitors'] = self.last_node

        def block4():
            self._event_def_()
        self._positive_closure(block4)

        self.ast['event_defs'] = self.last_node
        self._check_eof()

        self.ast._define(
            ['object', 'monitors', 'event_defs'],
            []
        )

    @graken()
    def _new_mon_(self):
        self._token('new')
        self._identifier_()
        self.ast['monitor'] = self.last_node
        with self._optional():
            self._token('(')
            self._identifier_list_()
            self.ast['monitor_params'] = self.last_node
            self._token(')')
        self._token('=')
        self._token('create')
        self._structure_()
        self.ast['struct'] = self.last_node

        self.ast._define(
            ['monitor', 'monitor_params', 'struct'],
            []
        )

    @graken()
    def _structure_(self):
        self._identifier_()
        self.ast['struct_id'] = self.last_node
        self._token('{')

        def block2():
            self._field_()
        self._closure(block2)
        self.ast['fields'] = self.last_node
        self._token('}')

        self.ast._define(
            ['struct_id', 'fields'],
            []
        )

    @graken()
    def _field_(self):
        self._identifier_()
        self.ast['variable'] = self.last_node
        self._token('=')
        self._expression_()
        self.ast['value'] = self.last_node
        self._token(';')

        self.ast._define(
            ['variable', 'value'],
            []
        )

    @graken()
    def _event_def_(self):
        self._identifier_()
        self.ast['monitor'] = self.last_node
        self._token('(')
        self._identifier_list_()
        self.ast['monitor_params'] = self.last_node
        self._token(').')
        self._identifier_()
        self.ast['event'] = self.last_node
        self._token('(')
        with self._optional():
            self._state_update_list_()
            self.ast['event_params'] = self.last_node
        self._token(')')
        self._token('=')

        def block4():
            with self._choice():
                with self._option():
                    self._token('update(')
                    self._expression_list_()
                    self.ast['update_params'] = self.last_node
                    self._token(')')
                with self._option():
                    self._token('call(')
                    self._expression_list_()
                    self.ast['call_params'] = self.last_node
                    self._token(')')
                self._error('no available options')
        self._closure(block4)
        with self._optional():
            self._token('when')
            self._expression_list_()
            self.ast['when'] = self.last_node
        with self._optional():
            self._action_()
            self.ast['event_action'] = self.last_node

        self.ast._define(
            ['monitor', 'monitor_params', 'event', 'event_params', 'update_params', 'call_params', 'when', 'event_action'],
            []
        )

    @graken()
    def _action_(self):
        self._token('{')
        self._nonempty_action_item_list_()
        self.ast.setlist('actions', self.last_node)
        self._token('}')

        self.ast._define(
            [],
            ['actions']
        )

    @graken()
    def _action_item_(self):
        with self._choice():
            with self._option():
                self._state_update_()
                self.ast['state_update'] = self.last_node
            with self._option():
                self._raise_stmt_()
                self.ast['raise_'] = self.last_node
            with self._option():
                self._instantiation_stmt_()
                self.ast['instantiation'] = self.last_node
            self._error('no available options')

        self.ast._define(
            ['state_update', 'raise', 'instantiation'],
            []
        )

    @graken()
    def _state_update_(self):
        with self._choice():
            with self._option():
                self._target_()
                self.ast['target'] = self.last_node
                self._token('=')
                self._expression_()
                self.ast['expression'] = self.last_node
            with self._option():
                self._target_()
                self.ast['target'] = self.last_node
                self._token('(')
                self._expression_list_()
                self.ast.setlist('expression_list', self.last_node)
                self._token(')')
            self._error('no available options')

        self.ast._define(
            ['target', 'expression'],
            ['expression_list']
        )

    @graken()
    def _raise_stmt_(self):
        self._token('raise')
        self._identifier_()
        self.ast['id'] = self.last_node
        with self._optional():
            self._token('(')
            self._expression_list_()
            self.ast.setlist('expr_list', self.last_node)
            self._token(')')

        self.ast._define(
            ['id'],
            ['expr_list']
        )

    @graken()
    def _instantiation_stmt_(self):
        self._token('new')
        self._identifier_()
        self.ast['id'] = self.last_node
        with self._optional():
            self._token('(')
            self._state_update_list_()
            self.ast.setlist('state_update_list', self.last_node)
            self._token(')')

        self.ast._define(
            ['id'],
            ['state_update_list']
        )

    @graken()
    def _type_(self):
        self._pattern(r'[a-zA-Z][A-Za-z0-9_]*')

    @graken()
    def _identifier_(self):
        self._pattern(r'[a-zA-Z][A-Za-z0-9_]*')

    @graken()
    def _integer_(self):
        self._pattern(r'[-+]?[0-9]+')

    @graken()
    def _float_(self):
        self._pattern(r'[-+]?[0-9]*\.?[0-9]+')

    @graken()
    def _expression_(self):
        with self._choice():
            with self._option():
                self._and_expr_()
                self.ast['or_ex'] = self.last_node

                def block1():
                    self._token('||')
                    self._and_expr_()
                    self.ast['or_ex'] = self.last_node
                self._positive_closure(block1)
            with self._option():
                self._and_expr_()
                self.ast['@'] = self.last_node
            self._error('no available options')

        self.ast._define(
            ['or_ex'],
            []
        )

    @graken()
    def _and_expr_(self):
        with self._choice():
            with self._option():
                self._sub_expr_()
                self.ast['and_ex'] = self.last_node

                def block1():
                    self._token('&&')
                    self._sub_expr_()
                    self.ast['and_ex'] = self.last_node
                self._positive_closure(block1)
            with self._option():
                self._sub_expr_()
                self.ast['@'] = self.last_node
            self._error('no available options')

        self.ast._define(
            ['and_ex'],
            []
        )

    @graken()
    def _sub_expr_(self):
        with self._choice():
            with self._option():

                def block0():
                    self._token('!!')
                self._closure(block0)
                self._token('!(')
                self._expression_()
                self.ast['not_ex'] = self.last_node
                self._token(')')
            with self._option():

                def block2():
                    self._token('!!')
                self._closure(block2)
                self._token('(')
                self._expression_()
                self.ast['@'] = self.last_node
                self._token(')')
            with self._option():
                self._comp_expr_()
                self.ast['@'] = self.last_node
            self._error('no available options')

        self.ast._define(
            ['not_ex'],
            []
        )

    @graken()
    def _comp_expr_(self):
        with self._choice():
            with self._option():
                self._arith_expr_()
                self.ast['comp'] = self.last_node

                def block1():
                    with self._group():
                        with self._choice():
                            with self._option():
                                self._token('>')
                            with self._option():
                                self._token('<')
                            with self._option():
                                self._token('>=')
                            with self._option():
                                self._token('<=')
                            with self._option():
                                self._token('==')
                            with self._option():
                                self._token('!=')
                            self._error('expecting one of: != < <= == > >=')
                    self.ast['operator'] = self.last_node
                    self._arith_expr_()
                    self.ast['comp'] = self.last_node
                self._positive_closure(block1)
            with self._option():
                self._token('(')
                self._comp_expr_()
                self.ast['@'] = self.last_node
                self._token(')')
            with self._option():
                self._arith_expr_()
                self.ast['@'] = self.last_node
            self._error('no available options')

        self.ast._define(
            ['comp', 'operator'],
            []
        )

    @graken()
    def _arith_expr_(self):
        with self._choice():
            with self._option():
                self._term_()
                self.ast['arith'] = self.last_node

                def block1():
                    with self._group():
                        with self._choice():
                            with self._option():
                                self._token('+')
                            with self._option():
                                self._token('-')
                            with self._option():
                                self._token('*')
                            with self._option():
                                self._token('/')
                            with self._option():
                                self._token('%')
                            self._error('expecting one of: % * + - /')
                    self.ast['operator'] = self.last_node
                    self._term_()
                    self.ast['arith'] = self.last_node
                self._positive_closure(block1)
            with self._option():
                self._term_()
                self.ast['@'] = self.last_node
            self._error('no available options')

        self.ast._define(
            ['arith', 'operator'],
            []
        )

    @graken()
    def _term_(self):
        with self._choice():
            with self._option():

                def block0():
                    with self._group():
                        with self._choice():
                            with self._option():
                                self._token('+')
                            with self._option():
                                self._token('-')
                            with self._option():
                                self._token('~')
                            with self._option():
                                self._token('!')
                            self._error('expecting one of: ! + - ~')
                    self.ast['unary'] = self.last_node
                self._closure(block0)
                self._atom_()
                self.ast['atom'] = self.last_node

                def block4():
                    self._trailer_()
                    self.ast['trailer'] = self.last_node
                self._closure(block4)
            with self._option():

                def block6():
                    with self._group():
                        with self._choice():
                            with self._option():
                                self._token('+')
                            with self._option():
                                self._token('-')
                            with self._option():
                                self._token('~')
                            self._error('expecting one of: + - ~')
                    self.ast['unary'] = self.last_node
                self._closure(block6)
                self._token('(')
                self._arith_expr_()
                self.ast['@'] = self.last_node
                self._token(')')
            self._error('no available options')

        self.ast._define(
            ['unary', 'atom', 'trailer'],
            []
        )

    @graken()
    def _atom_(self):
        with self._choice():
            with self._option():
                self._integer_()
            with self._option():
                self._float_()
            with self._option():
                self._identifier_()
            with self._option():
                self._token('true')
            with self._option():
                self._token('false')
            with self._option():
                self._token('null')
            self._error('expecting one of: false null true')

    @graken()
    def _trailer_(self):
        with self._choice():
            with self._option():
                self._token('[')
                with self._optional():
                    self._expression_()
                    self.ast['index'] = self.last_node
                self._token(']')
            with self._option():
                self._token('(')
                with self._optional():
                    self._expression_list_()
                    self.ast['params'] = self.last_node
                self._token(')')
            with self._option():
                self._token('.')
                self._identifier_()
                self.ast['dot'] = self.last_node

                def block3():
                    self._trailer_()
                    self.ast['trailer'] = self.last_node
                self._closure(block3)
            self._error('expecting one of: ( [')

        self.ast._define(
            ['index', 'params', 'dot', 'trailer'],
            []
        )

    @graken()
    def _target_(self):
        self._identifier_()

    @graken()
    def _expression_list_(self):
        with self._choice():
            with self._option():
                self._expression_()
                self.ast['@'] = self.last_node

                def block1():
                    self._token(',')
                    self._expression_()
                    self.ast['@'] = self.last_node
                self._closure(block1)
            with self._option():
                pass
            self._error('no available options')

    @graken()
    def _identifier_list_(self):
        with self._choice():
            with self._option():
                self._identifier_()
                self.ast['@'] = self.last_node

                def block1():
                    self._token(',')
                    self._identifier_()
                    self.ast['@'] = self.last_node
                self._closure(block1)
            with self._option():
                pass
            self._error('no available options')

    @graken()
    def _state_update_list_(self):
        with self._choice():
            with self._option():
                self._state_update_()
                self.ast['@'] = self.last_node

                def block1():
                    self._token(',')
                    self._state_update_()
                    self.ast['@'] = self.last_node
                self._closure(block1)
            with self._option():
                pass
            self._error('no available options')

    @graken()
    def _nonempty_action_item_list_(self):
        self._action_item_()
        self.ast['@'] = self.last_node

        def block1():
            self._token(';')
            self._action_item_()
            self.ast['@'] = self.last_node
        self._closure(block1)


class pedlSemantics(object):
    def object(self, ast):
        return ast

    def new_mon(self, ast):
        return ast

    def structure(self, ast):
        return ast

    def field(self, ast):
        return ast

    def event_def(self, ast):
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

    def sub_expr(self, ast):
        return ast

    def comp_expr(self, ast):
        return ast

    def arith_expr(self, ast):
        return ast

    def term(self, ast):
        return ast

    def atom(self, ast):
        return ast

    def trailer(self, ast):
        return ast

    def target(self, ast):
        return ast

    def expression_list(self, ast):
        return ast

    def identifier_list(self, ast):
        return ast

    def state_update_list(self, ast):
        return ast

    def nonempty_action_item_list(self, ast):
        return ast


def main(filename, startrule, trace=False, whitespace=None, nameguard=None):
    import json
    with open(filename) as f:
        text = f.read()
    parser = pedlParser(parseinfo=False)
    ast = parser.parse(
        text,
        startrule,
        filename=filename,
        trace=trace,
        whitespace=whitespace,
        nameguard=nameguard)
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
            for r in pedlParser.rule_list():
                print(r)
            print()
            sys.exit(0)

    parser = argparse.ArgumentParser(description="Simple parser for pedl.")
    parser.add_argument('-l', '--list', action=ListRules, nargs=0,
                        help="list all rules and exit")
    parser.add_argument('-n', '--no-nameguard', action='store_true',
                        dest='no_nameguard',
                        help="disable the 'nameguard' feature")
    parser.add_argument('-t', '--trace', action='store_true',
                        help="output trace information")
    parser.add_argument('-w', '--whitespace', type=str, default=string.whitespace,
                        help="whitespace specification")
    parser.add_argument('file', metavar="FILE", help="the input file to parse")
    parser.add_argument('startrule', metavar="STARTRULE",
                        help="the start rule for parsing")
    args = parser.parse_args()

    main(
        args.file,
        args.startrule,
        trace=args.trace,
        whitespace=args.whitespace,
        nameguard=not args.no_nameguard
    )
