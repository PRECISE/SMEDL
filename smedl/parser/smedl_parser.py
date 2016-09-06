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

from grako.buffering import Buffer
from grako.parsing import graken, Parser
from grako.util import re, RE_FLAGS, generic_main  # noqa


__version__ = (2016, 8, 29, 15, 31, 5, 0)

__all__ = [
    'smedlParser',
    'smedlSemantics',
    'main'
]

KEYWORDS = set([])


class smedlBuffer(Buffer):
    def __init__(self,
                 text,
                 whitespace=None,
                 nameguard=None,
                 comments_re=None,
                 eol_comments_re=None,
                 ignorecase=None,
                 namechars='',
                 **kwargs):
        super(smedlBuffer, self).__init__(
            text,
            whitespace=whitespace,
            nameguard=nameguard,
            comments_re=comments_re,
            eol_comments_re=eol_comments_re,
            ignorecase=ignorecase,
            namechars=namechars,
            **kwargs
        )


class smedlParser(Parser):
    def __init__(self,
                 whitespace=None,
                 nameguard=None,
                 comments_re=None,
                 eol_comments_re=None,
                 ignorecase=None,
                 left_recursion=True,
                 parseinfo=True,
                 keywords=KEYWORDS,
                 namechars='',
                 **kwargs):
        super(smedlParser, self).__init__(
            whitespace=whitespace,
            nameguard=nameguard,
            comments_re=comments_re,
            eol_comments_re=eol_comments_re,
            ignorecase=ignorecase,
            left_recursion=left_recursion,
            parseinfo=parseinfo,
            keywords=keywords,
            namechars=namechars,
            **kwargs
        )

    def parse(self, text, *args, **kwargs):
        if not isinstance(text, Buffer):
            text = smedlBuffer(text, **kwargs)
        return super(smedlParser, self).parse(text, *args, **kwargs)

    @graken()
    def _object_(self):

        def block1():
            self._import_definition_()
        self._closure(block1)
        self.add_last_node_to_name('imports')
        self._token('object')
        self._identifier_()
        self.name_last_node('object')
        with self._optional():
            self._token('identity')

            def block4():
                self._variable_declaration_()
            self._positive_closure(block4)
            self.add_last_node_to_name('identity')
        with self._optional():
            self._token('state')

            def block6():
                self._variable_declaration_()
            self._positive_closure(block6)
            self.add_last_node_to_name('state')
        self._token('events')

        def block7():
            with self._choice():
                with self._option():
                    self._token('internal')
                    self._event_definition_list_()
                    self.add_last_node_to_name('internal_events')
                with self._option():
                    self._token('exported')
                    self._event_definition_list_()
                    self.add_last_node_to_name('exported_events')
                self._error('no available options')
        self._closure(block7)
        self._token('imported')
        self._event_definition_list_()
        self.add_last_node_to_name('imported_events')

        def block12():
            with self._choice():
                with self._option():
                    self._token('imported')
                    self._event_definition_list_()
                    self.add_last_node_to_name('imported_events')
                with self._option():
                    self._token('internal')
                    self._event_definition_list_()
                    self.add_last_node_to_name('internal_events')
                with self._option():
                    self._token('exported')
                    self._event_definition_list_()
                    self.add_last_node_to_name('exported_events')
                self._error('no available options')
        self._closure(block12)
        self._token('scenarios')

        def block18():
            self._scenario_definition_()
        self._positive_closure(block18)
        self.add_last_node_to_name('scenarios')
        self._check_eof()
        self.ast._define(
            ['object'],
            ['exported_events', 'identity', 'imported_events', 'imports', 'internal_events', 'scenarios', 'state']
        )

    @graken()
    def _variable_declaration_(self):
        self._type_()
        self.name_last_node('type')
        self._identifier_()
        self.name_last_node('var')

        def block2():
            self._token(',')
            self._identifier_()
            self.name_last_node('var')
        self._closure(block2)
        self._token(';')
        self.ast._define(
            ['type', 'var'],
            []
        )

    @graken()
    def _import_definition_(self):
        self._token('#import')
        self._identifier_()
        self.name_last_node('import_id')
        self.ast._define(
            ['import_id'],
            []
        )

    @graken()
    def _event_definition_(self):
        with self._optional():
            self._token('error')
        self.name_last_node('error')
        self._identifier_()
        self.name_last_node('event_id')
        with self._optional():
            self._token('(')
            self._parameter_list_()
            self.name_last_node('params')
            self._token(')')
        with self._optional():
            self._token('=')
            self._expression_()
            self.name_last_node('definition')
        self.ast._define(
            ['definition', 'error', 'event_id', 'params'],
            []
        )

    @graken()
    def _scenario_definition_(self):
        with self._optional():
            self._token('atomic')
        self.name_last_node('atomic')
        self._identifier_()
        self.name_last_node('scenario_id')
        self._token(':')

        def block3():
            self._trace_definition_()
        self._positive_closure(block3)
        self.name_last_node('traces')
        self.ast._define(
            ['atomic', 'scenario_id', 'traces'],
            []
        )

    @graken()
    def _trace_definition_(self):
        self._identifier_()
        self.name_last_node('start_state')
        self._token('->')

        def block1():
            self._step_definition_()
            self.add_last_node_to_name('trace_steps')
            self._token('->')
        self._positive_closure(block1)
        self._identifier_()
        self.name_last_node('end_state')
        with self._optional():
            self._token('else')
            with self._optional():
                self._actions_()
                self.name_last_node('else_actions')
            self._token('->')
            self._identifier_()
            self.name_last_node('else_state')
        self.ast._define(
            ['else_actions', 'else_state', 'end_state', 'start_state'],
            ['trace_steps']
        )

    @graken()
    def _step_definition_(self):
        self._event_instance_()
        self.name_last_node('step_event')
        with self._optional():
            self._actions_()
            self.name_last_node('step_actions')
        self.ast._define(
            ['step_actions', 'step_event'],
            []
        )

    @graken()
    def _event_instance_(self):
        self._expression_()
        self.name_last_node('expression')
        with self._optional():
            self._token('when')
            self._expression_()
            self.name_last_node('when')
        self.ast._define(
            ['expression', 'when'],
            []
        )

    @graken()
    def _actions_(self):
        self._token('{')
        self._action_item_list_()
        self.name_last_node('actions')
        self._token('}')
        self.ast._define(
            ['actions'],
            []
        )

    @graken()
    def _action_item_(self):
        with self._choice():
            with self._option():
                self._state_update_()
                self.name_last_node('state_update')
            with self._option():
                self._raise_stmt_()
                self.name_last_node('raise_stmt')
            with self._option():
                self._instantiation_stmt_()
                self.name_last_node('instantiation')
            with self._option():
                self._call_stmt_()
                self.name_last_node('call_stmt')
            self._error('no available options')
        self.ast._define(
            ['call_stmt', 'instantiation', 'raise_stmt', 'state_update'],
            []
        )

    @graken()
    def _state_update_(self):
        with self._choice():
            with self._option():
                self._target_()
                self.name_last_node('target')
                with self._group():
                    with self._choice():
                        with self._option():
                            self._token('++')
                        with self._option():
                            self._token('--')
                        self._error('expecting one of: ++ --')
                self.name_last_node('operator')
            with self._option():
                self._target_()
                self.name_last_node('target')
                self._token('=')
                self.name_last_node('operator')
                self._expression_()
                self.name_last_node('expression')
            self._error('no available options')
        self.ast._define(
            ['expression', 'operator', 'target'],
            []
        )

    @graken()
    def _raise_stmt_(self):
        self._token('raise')
        self._identifier_()
        self.name_last_node('id')
        with self._optional():
            self._token('(')
            self._expression_list_()
            self.add_last_node_to_name('expr_list')
            self._token(')')
        self.ast._define(
            ['id'],
            ['expr_list']
        )

    @graken()
    def _instantiation_stmt_(self):
        self._token('new')
        self._identifier_()
        self.name_last_node('id')
        with self._optional():
            self._token('(')
            self._state_update_list_()
            self.add_last_node_to_name('state_update_list')
            self._token(')')
        self.ast._define(
            ['id'],
            ['state_update_list']
        )

    @graken()
    def _call_stmt_(self):
        self._target_()
        self.name_last_node('target')
        self._token('(')
        self._expression_list_()
        self.add_last_node_to_name('expr_list')
        self._token(')')
        self.ast._define(
            ['target'],
            ['expr_list']
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
                self.name_last_node('or_ex')

                def block1():
                    self._token('||')
                    self._and_expr_()
                    self.name_last_node('or_ex')
                self._positive_closure(block1)
            with self._option():
                self._and_expr_()
                self.name_last_node('@')
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
                self.name_last_node('and_ex')

                def block1():
                    self._token('&&')
                    self._sub_expr_()
                    self.name_last_node('and_ex')
                self._positive_closure(block1)
            with self._option():
                self._sub_expr_()
                self.name_last_node('@')
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
                self.name_last_node('not_ex')
                self._token(')')
            with self._option():

                def block2():
                    self._token('!!')
                self._closure(block2)
                self._token('(')
                self._expression_()
                self.name_last_node('@')
                self._token(')')
            with self._option():
                self._comp_expr_()
                self.name_last_node('@')
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
                self.name_last_node('comp')

                def block1():
                    with self._group():
                        with self._choice():
                            with self._option():
                                self._token('>=')
                            with self._option():
                                self._token('<=')
                            with self._option():
                                self._token('==')
                            with self._option():
                                self._token('!=')
                            with self._option():
                                self._token('>')
                            with self._option():
                                self._token('<')
                            self._error('expecting one of: != < <= == > >=')
                    self.name_last_node('operator')
                    self._arith_expr_()
                    self.name_last_node('comp')
                self._positive_closure(block1)
            with self._option():
                self._token('(')
                self._comp_expr_()
                self.name_last_node('@')
                self._token(')')
            with self._option():
                self._arith_expr_()
                self.name_last_node('@')
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
                self.name_last_node('arith')

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
                    self.name_last_node('operator')
                    self._term_()
                    self.name_last_node('arith')
                self._positive_closure(block1)
            with self._option():
                self._term_()
                self.name_last_node('@')
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
                    self.name_last_node('unary')
                self._closure(block0)
                self._atom_()
                self.name_last_node('atom')

                def block4():
                    self._trailer_()
                    self.name_last_node('trailer')
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
                    self.name_last_node('unary')
                self._closure(block6)
                self._token('(')
                self._arith_expr_()
                self.name_last_node('@')
                self._token(')')
            self._error('no available options')
        self.ast._define(
            ['atom', 'trailer', 'unary'],
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
                    self.name_last_node('index')
                self._token(']')
            with self._option():
                self._token('(')
                with self._optional():
                    self._expression_list_()
                    self.name_last_node('params')
                self._token(')')
            with self._option():
                self._token('.')
                self._identifier_()
                self.name_last_node('dot')

                def block3():
                    self._trailer_()
                    self.name_last_node('trailer')
                self._closure(block3)
            self._error('expecting one of: ( [')
        self.ast._define(
            ['dot', 'index', 'params', 'trailer'],
            []
        )

    @graken()
    def _target_(self):
        self._identifier_()

    @graken()
    def _parameter_list_(self):
        with self._choice():
            with self._option():
                self._type_()
                self.name_last_node('@')

                def block1():
                    self._token(',')
                    self._type_()
                    self.name_last_node('@')
                self._closure(block1)
            with self._option():
                pass
            self._error('no available options')

    @graken()
    def _expression_list_(self):
        with self._choice():
            with self._option():
                self._expression_()
                self.name_last_node('@')

                def block1():
                    self._token(',')
                    self._expression_()
                    self.name_last_node('@')
                self._closure(block1)
            with self._option():
                pass
            self._error('no available options')

    @graken()
    def _event_definition_list_(self):
        self._event_definition_()
        self.name_last_node('@')

        def block1():
            self._token(',')
            self._event_definition_()
            self.name_last_node('@')
        self._closure(block1)
        self._token(';')

    @graken()
    def _identifier_list_(self):
        with self._choice():
            with self._option():
                self._identifier_()
                self.name_last_node('@')

                def block1():
                    self._token(',')
                    self._identifier_()
                    self.name_last_node('@')
                self._closure(block1)
            with self._option():
                pass
            self._error('no available options')

    @graken()
    def _state_update_list_(self):
        with self._choice():
            with self._option():
                self._state_update_()
                self.name_last_node('@')

                def block1():
                    self._token(',')
                    self._state_update_()
                    self.name_last_node('@')
                self._closure(block1)
            with self._option():
                pass
            self._error('no available options')

    @graken()
    def _action_item_list_(self):
        self._action_item_()
        self.name_last_node('@')
        self._token(';')

        def block1():
            self._action_item_()
            self.name_last_node('@')
            self._token(';')
        self._closure(block1)


class smedlSemantics(object):
    def object(self, ast):
        return ast

    def variable_declaration(self, ast):
        return ast

    def import_definition(self, ast):
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

    def actions(self, ast):
        return ast

    def action_item(self, ast):
        return ast

    def state_update(self, ast):
        return ast

    def raise_stmt(self, ast):
        return ast

    def instantiation_stmt(self, ast):
        return ast

    def call_stmt(self, ast):
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

    def parameter_list(self, ast):
        return ast

    def expression_list(self, ast):
        return ast

    def event_definition_list(self, ast):
        return ast

    def identifier_list(self, ast):
        return ast

    def state_update_list(self, ast):
        return ast

    def action_item_list(self, ast):
        return ast


def main(
        filename,
        startrule,
        trace=False,
        whitespace=None,
        nameguard=None,
        comments_re=None,
        eol_comments_re=None,
        ignorecase=None,
        left_recursion=True,
        parseinfo=True,
        **kwargs):

    with open(filename) as f:
        text = f.read()
    whitespace = whitespace or None
    parser = smedlParser(parseinfo=False)
    ast = parser.parse(
        text,
        startrule,
        filename=filename,
        trace=trace,
        whitespace=whitespace,
        nameguard=nameguard,
        ignorecase=ignorecase,
        **kwargs)
    return ast

if __name__ == '__main__':
    import json
    ast = generic_main(main, smedlParser, name='smedl')
    print('AST:')
    print(ast)
    print()
    print('JSON:')
    print(json.dumps(ast, indent=2))
    print()
