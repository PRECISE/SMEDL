#!/usr/bin/env python
# -*- coding: utf-8 -*-

# CAVEAT UTILITOR
#
# This file was automatically generated by TatSu.
#
#    https://pypi.python.org/pypi/tatsu/
#
# Any changes you make to it will be overwritten the next time
# the file is generated.


from __future__ import print_function, division, absolute_import, unicode_literals

import sys

from tatsu.buffering import Buffer
from tatsu.parsing import Parser
from tatsu.parsing import tatsumasu, leftrec, nomemo
from tatsu.parsing import leftrec, nomemo  # noqa
from tatsu.util import re, generic_main  # noqa


KEYWORDS = {}  # type: ignore


class SMEDLBuffer(Buffer):
    def __init__(
        self,
        text,
        whitespace=None,
        nameguard=None,
        comments_re='(\\/\\*([^*]|[\\r\\n]|(\\*+([^*\\/]|[\\r\\n])))*\\*+\\/)|(\\/\\/.*)',
        eol_comments_re=None,
        ignorecase=None,
        namechars='',
        **kwargs
    ):
        super(SMEDLBuffer, self).__init__(
            text,
            whitespace=whitespace,
            nameguard=nameguard,
            comments_re=comments_re,
            eol_comments_re=eol_comments_re,
            ignorecase=ignorecase,
            namechars=namechars,
            **kwargs
        )


class SMEDLParser(Parser):
    def __init__(
        self,
        whitespace=None,
        nameguard=None,
        comments_re='(\\/\\*([^*]|[\\r\\n]|(\\*+([^*\\/]|[\\r\\n])))*\\*+\\/)|(\\/\\/.*)',
        eol_comments_re=None,
        ignorecase=None,
        left_recursion=True,
        parseinfo=False,
        keywords=None,
        namechars='',
        buffer_class=SMEDLBuffer,
        **kwargs
    ):
        if keywords is None:
            keywords = KEYWORDS
        super(SMEDLParser, self).__init__(
            whitespace=whitespace,
            nameguard=nameguard,
            comments_re=comments_re,
            eol_comments_re=eol_comments_re,
            ignorecase=ignorecase,
            left_recursion=left_recursion,
            parseinfo=parseinfo,
            keywords=keywords,
            namechars=namechars,
            buffer_class=buffer_class,
            **kwargs
        )

    @tatsumasu()
    def _identifier_list_(self):  # noqa

        def sep0():
            self._token(',')

        def block0():
            self._identifier_()
        self._gather(block0, sep0)

    @tatsumasu()
    def _identifier_(self):  # noqa
        self._pattern('[a-zA-Z][A-Za-z0-9_]*')

    @tatsumasu()
    def _type_list_(self):  # noqa

        def sep0():
            self._token(',')

        def block0():
            self._type_()
        self._gather(block0, sep0)

    @tatsumasu()
    def _type_(self):  # noqa
        with self._choice():
            with self._option():
                self._token('int')
            with self._option():
                self._token('float')
            with self._option():
                self._token('double')
                self._constant('float')
                self.name_last_node('@')
            with self._option():
                self._token('char')
            with self._option():
                self._token('string')
            with self._option():
                self._token('pointer')
            with self._option():
                self._token('thread')
            with self._option():
                self._token('opaque')
            self._error('no available options')

    @tatsumasu()
    def _start_(self):  # noqa
        self._declaration_()
        self.name_last_node('name')
        self._helper_list_()
        self.name_last_node('helpers')
        self._state_section_()
        self.name_last_node('state_vars')
        self._event_section_()
        self.name_last_node('events')
        self._scenario_section_()
        self.name_last_node('scenarios')
        self._check_eof()
        self.ast._define(
            ['events', 'helpers', 'name', 'scenarios', 'state_vars'],
            []
        )

    @tatsumasu()
    def _declaration_(self):  # noqa
        self._token('object')
        self._identifier_()
        self.name_last_node('@')
        self._token(';')

    @tatsumasu()
    def _helper_list_(self):  # noqa

        def block0():
            self._helper_definition_()
        self._closure(block0)

    @tatsumasu()
    def _helper_definition_(self):  # noqa
        self._token('#include')
        self._helper_filename_()
        self.name_last_node('@')

    @tatsumasu()
    def _helper_filename_(self):  # noqa
        self._pattern('"[^"\\n\\r\\v\\f]*"|<[^>\\n\\r\\v\\f]*>')

    @tatsumasu()
    def _state_section_(self):  # noqa
        self._token('state:')

        def block1():
            self._state_declaration_()
        self._closure(block1)
        self.name_last_node('@')

    @tatsumasu()
    def _state_declaration_(self):  # noqa
        self._type_()
        self.name_last_node('type')
        self._identifier_()
        self.name_last_node('name')
        with self._optional():
            self._token('=')
            self._signed_literal_()
            self.name_last_node('value')
        self._token(';')
        self.ast._define(
            ['name', 'type', 'value'],
            []
        )

    @tatsumasu()
    def _event_section_(self):  # noqa
        self._token('events:')

        def block1():
            self._event_declaration_()
        self._closure(block1)
        self.name_last_node('@')

    @tatsumasu()
    def _event_declaration_(self):  # noqa
        with self._group():
            with self._choice():
                with self._option():
                    self._token('imported')
                with self._option():
                    self._token('internal')
                with self._option():
                    self._token('exported')
                self._error('no available options')
        self.name_last_node('type')

        def sep3():
            self._token(',')

        def block3():
            self._event_signature_()
        self._positive_gather(block3, sep3)
        self.name_last_node('signatures')
        self._token(';')
        self.ast._define(
            ['signatures', 'type'],
            []
        )

    @tatsumasu()
    def _event_signature_(self):  # noqa
        self._identifier_()
        self.name_last_node('name')
        self._token('(')
        self._type_list_()
        self.name_last_node('params')
        self._token(')')
        self.ast._define(
            ['name', 'params'],
            []
        )

    @tatsumasu()
    def _scenario_section_(self):  # noqa
        self._token('scenarios:')

        def block1():
            self._scenario_()
        self._closure(block1)
        self.name_last_node('@')

    @tatsumasu()
    def _scenario_(self):  # noqa
        self._identifier_()
        self.name_last_node('name')
        self._token(':')

        def block2():
            self._transition_()
        self._closure(block2)
        self.name_last_node('transitions')
        self.ast._define(
            ['name', 'transitions'],
            []
        )

    @tatsumasu()
    def _transition_(self):  # noqa
        self._identifier_()
        self.name_last_node('start_state')
        self._token('->')
        self._step_definition_list_()
        self.name_last_node('steps')
        self._token('->')
        self._identifier_()
        self.name_last_node('end_state')
        with self._optional():
            self._else_definition_()
            self.name_last_node('else_step')
        self._token(';')
        self.ast._define(
            ['else_step', 'end_state', 'start_state', 'steps'],
            []
        )

    @tatsumasu()
    def _step_definition_list_(self):  # noqa

        def sep0():
            self._token('->')

        def block0():
            self._step_definition_()
        self._positive_gather(block0, sep0)

    @tatsumasu()
    def _step_definition_(self):  # noqa
        self._step_event_definition_()
        self.name_last_node('event')
        with self._optional():
            self._token('when')
            self._token('(')
            self._expression_()
            self.name_last_node('condition')
            self._token(')')
        with self._optional():
            self._action_list_()
            self.name_last_node('actions')
        self.ast._define(
            ['actions', 'condition', 'event'],
            []
        )

    @tatsumasu()
    def _else_definition_(self):  # noqa
        self._token('else')
        self._else_preproc_()
        with self._optional():
            self._action_list_()
            self.name_last_node('else_actions')
        self._token('->')
        self._identifier_()
        self.name_last_node('else_state')
        self.ast._define(
            ['else_actions', 'else_state'],
            []
        )

    @tatsumasu()
    def _else_preproc_(self):  # noqa
        self._void()

    @tatsumasu()
    def _step_event_definition_(self):  # noqa
        self._identifier_()
        self.name_last_node('name')
        self._token('(')
        self._identifier_list_()
        self.name_last_node('params')
        self._token(')')
        self.ast._define(
            ['name', 'params'],
            []
        )

    @tatsumasu()
    def _action_list_(self):  # noqa
        self._token('{')
        with self._group():
            with self._choice():
                with self._option():

                    def sep1():
                        self._token(';')

                    def block1():
                        self._action_()
                    self._positive_gather(block1, sep1)
                    self.name_last_node('@')
                    with self._optional():
                        self._token(';')
                with self._option():
                    self._empty_closure()
                    self.name_last_node('@')
                self._error('no available options')
        self._token('}')

    @tatsumasu()
    def _action_(self):  # noqa
        with self._choice():
            with self._option():
                self._assignment_()
            with self._option():
                self._increment_()
            with self._option():
                self._decrement_()
            with self._option():
                self._raise_stmt_()
            with self._option():
                self._call_stmt_()
            self._error('no available options')

    @tatsumasu()
    def _assignment_(self):  # noqa
        self._identifier_()
        self.name_last_node('target')
        self._token('=')
        self._expression_()
        self.name_last_node('value')
        self.ast._define(
            ['target', 'value'],
            []
        )

    @tatsumasu()
    def _increment_(self):  # noqa
        self._identifier_()
        self.name_last_node('target')
        self._token('++')
        self.ast._define(
            ['target'],
            []
        )

    @tatsumasu()
    def _decrement_(self):  # noqa
        self._identifier_()
        self.name_last_node('target')
        self._token('--')
        self.ast._define(
            ['target'],
            []
        )

    @tatsumasu()
    def _raise_stmt_(self):  # noqa
        self._token('raise')
        self._identifier_()
        self.name_last_node('event')
        self._token('(')
        self._expression_list_()
        self.name_last_node('params')
        self._token(')')
        self.ast._define(
            ['event', 'params'],
            []
        )

    @tatsumasu()
    def _call_stmt_(self):  # noqa
        self._identifier_()
        self.name_last_node('function')
        self._token('(')
        self._expression_list_()
        self.name_last_node('params')
        self._token(')')
        self.ast._define(
            ['function', 'params'],
            []
        )

    @tatsumasu()
    def _expression_list_(self):  # noqa

        def sep0():
            self._token(',')

        def block0():
            self._expression_()
        self._gather(block0, sep0)

    @tatsumasu()
    def _expression_(self):  # noqa
        self._or_expr_()

    @tatsumasu()
    def _or_expr_(self):  # noqa

        def sep0():
            self._token('||')

        def block0():
            self._and_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _and_expr_(self):  # noqa

        def sep0():
            self._token('&&')

        def block0():
            self._bitwise_or_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _bitwise_or_expr_(self):  # noqa

        def sep0():
            self._token('|')

        def block0():
            self._bitwise_xor_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _bitwise_xor_expr_(self):  # noqa

        def sep0():
            self._token('^')

        def block0():
            self._bitwise_and_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _bitwise_and_expr_(self):  # noqa

        def sep0():
            self._token('&')

        def block0():
            self._equality_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _equality_expr_(self):  # noqa

        def sep0():
            with self._group():
                with self._choice():
                    with self._option():
                        self._token('==')
                    with self._option():
                        self._token('!=')
                    self._error('no available options')

        def block0():
            self._comparison_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _comparison_expr_(self):  # noqa

        def sep0():
            with self._group():
                with self._choice():
                    with self._option():
                        self._token('<')
                    with self._option():
                        self._token('<=')
                    with self._option():
                        self._token('>')
                    with self._option():
                        self._token('>=')
                    self._error('no available options')

        def block0():
            self._bitshift_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _bitshift_expr_(self):  # noqa

        def sep0():
            with self._group():
                with self._choice():
                    with self._option():
                        self._token('<<')
                    with self._option():
                        self._token('>>')
                    self._error('no available options')

        def block0():
            self._additive_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _additive_expr_(self):  # noqa

        def sep0():
            with self._group():
                with self._choice():
                    with self._option():
                        self._token('+')
                    with self._option():
                        self._token('-')
                    self._error('no available options')

        def block0():
            self._multiplicative_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _multiplicative_expr_(self):  # noqa

        def sep0():
            with self._group():
                with self._choice():
                    with self._option():
                        self._token('*')
                    with self._option():
                        self._token('/')
                    with self._option():
                        self._token('%')
                    self._error('no available options')

        def block0():
            self._unary_expr_()
        self._left_join(block0, sep0)

    @tatsumasu()
    def _unary_expr_(self):  # noqa
        with self._choice():
            with self._option():
                self._token('+')
                self._cut()
                self._atom_()
            with self._option():
                self._token('-')
                self._cut()
                self._atom_()
            with self._option():
                self._token('~')
                self._cut()
                self._atom_()
            with self._option():
                self._token('!')
                self._cut()
                self._atom_()
            with self._option():
                self._atom_()
            self._error('no available options')

    @tatsumasu()
    def _atom_(self):  # noqa
        with self._choice():
            with self._option():
                self._literal_()
            with self._option():
                self._helper_call_()
            with self._option():
                self._parenthesized_()
            with self._option():
                self._var_or_param_()
            self._error('no available options')

    @tatsumasu()
    def _literal_(self):  # noqa
        with self._choice():
            with self._option():
                self._float_()
                self.name_last_node('value')
                self._constant('float')
                self.name_last_node('type')
            with self._option():
                self._integer_()
                self.name_last_node('value')
                self._constant('int')
                self.name_last_node('type')
            with self._option():
                self._char_()
                self.name_last_node('value')
                self._constant('char')
                self.name_last_node('type')
            with self._option():
                self._string_()
                self.name_last_node('value')
                self._constant('string')
                self.name_last_node('type')
            with self._option():
                self._bool_()
                self.name_last_node('value')
                self._constant('int')
                self.name_last_node('type')
            with self._option():
                self._null_()
                self.name_last_node('value')
                self._constant('null')
                self.name_last_node('type')
            self._error('no available options')
        self.ast._define(
            ['type', 'value'],
            []
        )

    @tatsumasu()
    def _helper_call_(self):  # noqa
        self._identifier_()
        self.name_last_node('function')
        self._token('(')
        self._cut()
        self._expression_list_()
        self.name_last_node('params')
        self._token(')')
        self.ast._define(
            ['function', 'params'],
            []
        )

    @tatsumasu()
    def _var_or_param_(self):  # noqa
        self._identifier_()

    @tatsumasu()
    def _parenthesized_(self):  # noqa
        self._token('(')
        self._cut()
        self._expression_()
        self.name_last_node('@')
        self._token(')')

    @tatsumasu()
    def _signed_literal_(self):  # noqa
        with self._choice():
            with self._option():
                with self._choice():
                    with self._option():
                        self._float_()
                        self.name_last_node('value')
                        self._constant('float')
                        self.name_last_node('type')
                    with self._option():
                        self._integer_()
                        self.name_last_node('value')
                        self._constant('int')
                        self.name_last_node('type')
                    with self._option():
                        self._char_()
                        self.name_last_node('value')
                        self._constant('char')
                        self.name_last_node('type')
                    with self._option():
                        self._string_()
                        self.name_last_node('value')
                        self._constant('string')
                        self.name_last_node('type')
                    with self._option():
                        self._bool_()
                        self.name_last_node('value')
                        self._constant('int')
                        self.name_last_node('type')
                    with self._option():
                        self._null_()
                        self.name_last_node('value')
                        self._constant('null')
                        self.name_last_node('type')
                    self._error('no available options')
            with self._option():
                with self._group():
                    self._token('+')
                    self._float_()
                self.name_last_node('value')
                self._constant('signed_float')
                self.name_last_node('type')
            with self._option():
                with self._group():
                    self._token('-')
                    self._float_()
                self.name_last_node('value')
                self._constant('signed_float')
                self.name_last_node('type')
            with self._option():
                with self._group():
                    self._token('+')
                    self._integer_()
                self.name_last_node('value')
                self._constant('signed_int')
                self.name_last_node('type')
            with self._option():
                with self._group():
                    self._token('-')
                    self._integer_()
                self.name_last_node('value')
                self._constant('signed_int')
                self.name_last_node('type')
            self._error('no available options')
        self.ast._define(
            ['type', 'value'],
            []
        )

    @tatsumasu()
    def _integer_(self):  # noqa
        self._pattern('[0-9]+')

    @tatsumasu()
    def _float_(self):  # noqa
        self._pattern('[0-9]+\\.(?:[Ee][+-]?[0-9]+)?|[0-9]*\\.[0-9]+(?:[Ee][+-]?[0-9]+)?|[0-9]+[Ee][+-]?[0-9]+')

    @tatsumasu()
    def _char_(self):  # noqa
        self._pattern("'(?:[^'\\\\\\n]|\\\\[0-7]{1,3}|\\\\x[0-9a-fA-F]+|\\\\u[0-9a-fA-F]{4}|\\\\U[0-9a-fA-F]{8}|\\\\[^0-7xuU])'")

    @tatsumasu()
    def _string_(self):  # noqa
        self._pattern('"[^"\\\\\\n]*(?:\\\\.[^"\\\\\\n]*)*"')

    @tatsumasu()
    def _bool_(self):  # noqa
        with self._choice():
            with self._option():
                self._token('true')
                self._constant(1)
                self.name_last_node('@')
            with self._option():
                self._token('false')
                self._constant(0)
                self.name_last_node('@')
            self._error('no available options')

    @tatsumasu()
    def _null_(self):  # noqa
        with self._choice():
            with self._option():
                self._token('NULL')
            with self._option():
                self._token('null')
                self._constant('NULL')
                self.name_last_node('@')
            self._error('no available options')


class SMEDLSemantics(object):
    def identifier_list(self, ast):  # noqa
        return ast

    def identifier(self, ast):  # noqa
        return ast

    def type_list(self, ast):  # noqa
        return ast

    def type(self, ast):  # noqa
        return ast

    def start(self, ast):  # noqa
        return ast

    def declaration(self, ast):  # noqa
        return ast

    def helper_list(self, ast):  # noqa
        return ast

    def helper_definition(self, ast):  # noqa
        return ast

    def helper_filename(self, ast):  # noqa
        return ast

    def state_section(self, ast):  # noqa
        return ast

    def state_declaration(self, ast):  # noqa
        return ast

    def event_section(self, ast):  # noqa
        return ast

    def event_declaration(self, ast):  # noqa
        return ast

    def event_signature(self, ast):  # noqa
        return ast

    def scenario_section(self, ast):  # noqa
        return ast

    def scenario(self, ast):  # noqa
        return ast

    def transition(self, ast):  # noqa
        return ast

    def step_definition_list(self, ast):  # noqa
        return ast

    def step_definition(self, ast):  # noqa
        return ast

    def else_definition(self, ast):  # noqa
        return ast

    def else_preproc(self, ast):  # noqa
        return ast

    def step_event_definition(self, ast):  # noqa
        return ast

    def action_list(self, ast):  # noqa
        return ast

    def action(self, ast):  # noqa
        return ast

    def assignment(self, ast):  # noqa
        return ast

    def increment(self, ast):  # noqa
        return ast

    def decrement(self, ast):  # noqa
        return ast

    def raise_stmt(self, ast):  # noqa
        return ast

    def call_stmt(self, ast):  # noqa
        return ast

    def expression_list(self, ast):  # noqa
        return ast

    def expression(self, ast):  # noqa
        return ast

    def or_expr(self, ast):  # noqa
        return ast

    def and_expr(self, ast):  # noqa
        return ast

    def bitwise_or_expr(self, ast):  # noqa
        return ast

    def bitwise_xor_expr(self, ast):  # noqa
        return ast

    def bitwise_and_expr(self, ast):  # noqa
        return ast

    def equality_expr(self, ast):  # noqa
        return ast

    def comparison_expr(self, ast):  # noqa
        return ast

    def bitshift_expr(self, ast):  # noqa
        return ast

    def additive_expr(self, ast):  # noqa
        return ast

    def multiplicative_expr(self, ast):  # noqa
        return ast

    def unary_expr(self, ast):  # noqa
        return ast

    def atom(self, ast):  # noqa
        return ast

    def literal(self, ast):  # noqa
        return ast

    def helper_call(self, ast):  # noqa
        return ast

    def var_or_param(self, ast):  # noqa
        return ast

    def parenthesized(self, ast):  # noqa
        return ast

    def signed_literal(self, ast):  # noqa
        return ast

    def integer(self, ast):  # noqa
        return ast

    def float(self, ast):  # noqa
        return ast

    def char(self, ast):  # noqa
        return ast

    def string(self, ast):  # noqa
        return ast

    def bool(self, ast):  # noqa
        return ast

    def null(self, ast):  # noqa
        return ast


def main(filename, start=None, **kwargs):
    if start is None:
        start = 'identifier_list'
    if not filename or filename == '-':
        text = sys.stdin.read()
    else:
        with open(filename) as f:
            text = f.read()
    parser = SMEDLParser()
    return parser.parse(text, rule_name=start, filename=filename, **kwargs)


if __name__ == '__main__':
    import json
    from tatsu.util import asjson

    ast = generic_main(main, SMEDLParser, name='SMEDL')
    print('AST:')
    print(ast)
    print()
    print('JSON:')
    print(json.dumps(asjson(ast), indent=2))
    print()
