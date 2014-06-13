#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# CAVEAT UTILITOR
# This file was automatically generated by Grako.
#    https://bitbucket.org/apalala/grako/
# Any changes you make to it will be overwritten the
# next time the file is generated.
#

from __future__ import print_function, division, absolute_import, unicode_literals
from grako.parsing import *  # noqa
from grako.exceptions import *  # noqa


__version__ = '14.163.23.10.30'


class GrakoParser(Parser):
    def __init__(self, whitespace=None, **kwargs):
        super(GrakoParser, self).__init__(whitespace=whitespace, **kwargs)

    @rule_def
    def _grammar_(self):

        def block1():
            self._rule_()
        self._positive_closure(block1)

        self.ast['@'] = self.last_node
        self._check_eof()

    @rule_def
    def _rule_(self):
        self._word_()
        self.ast['name'] = self.last_node
        self._token('=')
        self._cut()
        self._expre_()
        self.ast['rhs'] = self.last_node
        with self._group():
            with self._choice():
                with self._option():
                    self._token('.')
                with self._option():
                    self._token(';')
                self._error('expecting one of: ; .')
        self._cut()

    @rule_def
    def _expre_(self):
        with self._choice():
            with self._option():
                self._choice_()
            with self._option():
                self._sequence_()
            self._error('no available options')

    @rule_def
    def _choice_(self):
        self._sequence_()
        self.ast.add_list('options', self.last_node)

        def block1():
            self._token('|')
            self._cut()
            self._sequence_()
            self.ast['options'] = self.last_node
        self._positive_closure(block1)

    @rule_def
    def _sequence_(self):

        def block1():
            self._element_()
        self._positive_closure(block1)

        self.ast['sequence'] = self.last_node

    @rule_def
    def _element_(self):
        with self._choice():
            with self._option():
                self._named_()
            with self._option():
                self._override_()
            with self._option():
                self._term_()
            self._error('no available options')

    @rule_def
    def _named_(self):
        self._name_()
        self.ast['name'] = self.last_node
        with self._group():
            with self._choice():
                with self._option():
                    self._token('+:')
                    self.ast['force_list'] = self.last_node
                with self._option():
                    self._token(':')
                self._error('expecting one of: : +:')
        self._element_()
        self.ast['value'] = self.last_node

    @rule_def
    def _name_(self):
        with self._choice():
            with self._option():
                self._word_()
            with self._option():
                self._token('@')
            self._error('expecting one of: @')

    @rule_def
    def _override_(self):
        self._token('@')
        self._cut()
        self._element_()
        self.ast['@'] = self.last_node

    @rule_def
    def _term_(self):
        with self._choice():
            with self._option():
                self._void_()
            with self._option():
                self._group_()
            with self._option():
                self._closure_()
            with self._option():
                self._optional_()
            with self._option():
                self._special_()
            with self._option():
                self._kif_()
            with self._option():
                self._knot_()
            with self._option():
                self._atom_()
            self._error('no available options')

    @rule_def
    def _group_(self):
        self._token('(')
        self._cut()
        self._expre_()
        self.ast['@'] = self.last_node
        self._token(')')
        self._cut()

    @rule_def
    def _closure_(self):
        self._token('{')
        self._cut()
        self._expre_()
        self.ast['exp'] = self.last_node
        self._token('}')
        self._cut()
        with self._group():
            with self._choice():
                with self._option():
                    with self._group():
                        with self._choice():
                            with self._option():
                                self._token('-')
                            with self._option():
                                self._token('+')
                            self._error('expecting one of: + -')
                    self.ast['plus'] = self.last_node
                with self._option():
                    with self._optional():
                        self._token('*')
                self._error('expecting one of: + * -')
        self._cut()

    @rule_def
    def _optional_(self):
        self._token('[')
        self._cut()
        self._expre_()
        self.ast['@'] = self.last_node
        self._token(']')
        self._cut()

    @rule_def
    def _special_(self):
        self._token('?(')
        self._cut()
        self._pattern(r'(.*)')
        self.ast['@'] = self.last_node
        self._token(')?')
        self._cut()

    @rule_def
    def _kif_(self):
        self._token('&')
        self._cut()
        self._term_()
        self.ast['@'] = self.last_node

    @rule_def
    def _knot_(self):
        self._token('!')
        self._cut()
        self._term_()
        self.ast['@'] = self.last_node

    @rule_def
    def _atom_(self):
        with self._choice():
            with self._option():
                self._cut_()
            with self._option():
                self._token_()
            with self._option():
                self._call_()
            with self._option():
                self._pattern_()
            with self._option():
                self._eof_()
            self._error('no available options')

    @rule_def
    def _call_(self):
        self._word_()

    @rule_def
    def _void_(self):
        self._token('()')
        self._cut()

    @rule_def
    def _cut_(self):
        self._token('>>')
        self._cut()

    @rule_def
    def _token_(self):
        with self._choice():
            with self._option():
                self._token('"')
                self._cut()
                self._pattern(r'([^"\\\n]|\\"|\\\\)*')
                self.ast['@'] = self.last_node
                self._token('"')
            with self._option():
                self._token("'")
                self._cut()
                self._pattern(r"([^'\\\n]|\\'|\\\\)*")
                self.ast['@'] = self.last_node
                self._token("'")
            self._error('expecting one of: \' "')

    @rule_def
    def _word_(self):
        self._pattern(r'[-_A-Za-z0-9]+')

    @rule_def
    def _pattern_(self):
        self._token('?/')
        self._cut()
        self._pattern(r'(.*?)(?=/\?)')
        self.ast['@'] = self.last_node
        self._token('/?')
        self._cut()

    @rule_def
    def _eof_(self):
        self._token('$')
        self._cut()


class GrakoSemanticParser(CheckSemanticsMixin, GrakoParser):
    pass


class GrakoSemantics(object):
    def grammar(self, ast):
        return ast

    def rule(self, ast):
        return ast

    def expre(self, ast):
        return ast

    def choice(self, ast):
        return ast

    def sequence(self, ast):
        return ast

    def element(self, ast):
        return ast

    def named(self, ast):
        return ast

    def name(self, ast):
        return ast

    def override(self, ast):
        return ast

    def term(self, ast):
        return ast

    def group(self, ast):
        return ast

    def closure(self, ast):
        return ast

    def optional(self, ast):
        return ast

    def special(self, ast):
        return ast

    def kif(self, ast):
        return ast

    def knot(self, ast):
        return ast

    def atom(self, ast):
        return ast

    def call(self, ast):
        return ast

    def void(self, ast):
        return ast

    def cut(self, ast):
        return ast

    def token(self, ast):
        return ast

    def word(self, ast):
        return ast

    def pattern(self, ast):
        return ast

    def eof(self, ast):
        return ast


def main(filename, startrule, trace=False, whitespace=None):
    import json
    with open(filename) as f:
        text = f.read()
    parser = GrakoParser(parseinfo=False)
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
            for r in GrakoParser.rule_list():
                print(r)
            print()
            sys.exit(0)

    parser = argparse.ArgumentParser(description="Simple parser for Grako.")
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