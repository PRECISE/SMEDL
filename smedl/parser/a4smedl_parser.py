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


__version__ = (2017, 12, 1, 5, 22, 8, 4)

__all__ = [
    'a4smedlParser',
    'a4smedlSemantics',
    'main'
]

KEYWORDS = set([])


class a4smedlBuffer(Buffer):
    def __init__(self,
                 text,
                 whitespace=None,
                 nameguard=None,
                 comments_re=None,
                 eol_comments_re=None,
                 ignorecase=None,
                 namechars='',
                 **kwargs):
        super(a4smedlBuffer, self).__init__(
            text,
            whitespace=whitespace,
            nameguard=nameguard,
            comments_re=comments_re,
            eol_comments_re=eol_comments_re,
            ignorecase=ignorecase,
            namechars=namechars,
            **kwargs
        )


class a4smedlParser(Parser):
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
        super(a4smedlParser, self).__init__(
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
            text = a4smedlBuffer(text, **kwargs)
        return super(a4smedlParser, self).parse(text, *args, **kwargs)

    @graken()
    def _top_(self):
        self._token('System')
        self._identifier_()
        self.name_last_node('system')
        self._token(':=')
        self._monitorDeclaration_()
        self.name_last_node('monitor_declaration')
        self._architectureSpec_()
        self.name_last_node('archSpec')
        self._check_eof()
        self.ast._define(
            ['archSpec', 'monitor_declaration', 'system'],
            []
        )

    @graken()
    def _monitorDeclaration_(self):

        def block1():
            self._monitorInterface_()
        self._positive_closure(block1)
        self.add_last_node_to_name('interfaces')
        self.ast._define(
            [],
            ['interfaces']
        )

    @graken()
    def _monitorInterface_(self):
        with self._optional():
            with self._choice():
                with self._option():
                    self._token('Async')
                with self._option():
                    self._token('Sync')
                self._error('expecting one of: Async Sync')
        self.name_last_node('mon_type')
        self._identifier_()
        self.name_last_node('monitor_identifier')
        self._token('(')
        self._parameter_list_()
        self.name_last_node('params')
        self._token(')')
        self._token('{')

        def block4():
            self._token('imported')
            self._event_definition_list_()
            self.add_last_node_to_name('imported_events')
        self._closure(block4)

        def block6():
            self._token('exported')
            self._event_definition_list_()
            self.add_last_node_to_name('exported_events')
        self._closure(block6)
        self._token('}')
        self.ast._define(
            ['mon_type', 'monitor_identifier', 'params'],
            ['exported_events', 'imported_events']
        )

    @graken()
    def _event_definition_(self):
        with self._optional():
            self._token('creation')
        self.name_last_node('creation')
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
        self.ast._define(
            ['creation', 'error', 'event_id', 'params'],
            []
        )

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
    def _type_(self):
        self._pattern(r'[a-zA-Z][A-Za-z0-9_]*')

    @graken()
    def _identifier_(self):
        self._pattern(r'[a-zA-Z][A-Za-z0-9_]*')

    @graken()
    def _integer_(self):
        self._pattern(r'[-+]?[0-9]+')

    @graken()
    def _architectureSpec_(self):

        def block1():
            self._connectionExpr_()
        self._positive_closure(block1)
        self.add_last_node_to_name('conn_expr')
        self.ast._define(
            [],
            ['conn_expr']
        )

    @graken()
    def _connectionExpr_(self):
        with self._optional():
            self._identifier_()
            self.name_last_node('connection')
            self._token(':')
        with self._optional():
            self._identifier_()
            self.name_last_node('source_machine_identifier')
            self._token('.')
        self._identifier_()
        self.name_last_node('source_event_identifier')
        self._token('=>')
        self._identifier_()
        self.name_last_node('target_machine_identifier')
        self._token('.')
        self._identifier_()
        self.name_last_node('target_event_identifier')
        with self._optional():
            self._token('{')
            self._patternSpec_()
            self.name_last_node('pattern_spec')
            self._token('}')
        self.ast._define(
            ['connection', 'pattern_spec', 'source_event_identifier', 'source_machine_identifier', 'target_event_identifier', 'target_machine_identifier'],
            []
        )

    @graken()
    def _patternSpec_(self):
        self._patternExpr_()
        self.name_last_node('@')

        def block1():
            self._token(';')
            self._patternExpr_()
            self.name_last_node('@')
        self._closure(block1)

    @graken()
    def _patternExpr_(self):
        self._term_()
        self.name_last_node('left')
        with self._group():
            with self._choice():
                with self._option():
                    self._token('=')
                with self._option():
                    self._token('<>')
                self._error('expecting one of: <> =')
        self.name_last_node('operator')
        self._term_()
        self.name_last_node('right')
        self.ast._define(
            ['left', 'operator', 'right'],
            []
        )

    @graken()
    def _term_(self):
        self._identifier_()
        self.name_last_node('term_id')
        self._token('[')
        self._integer_()
        self.name_last_node('term_index')
        self._token(']')
        self.ast._define(
            ['term_id', 'term_index'],
            []
        )


class a4smedlSemantics(object):
    def top(self, ast):
        return ast

    def monitorDeclaration(self, ast):
        return ast

    def monitorInterface(self, ast):
        return ast

    def event_definition(self, ast):
        return ast

    def event_definition_list(self, ast):
        return ast

    def parameter_list(self, ast):
        return ast

    def type(self, ast):
        return ast

    def identifier(self, ast):
        return ast

    def integer(self, ast):
        return ast

    def architectureSpec(self, ast):
        return ast

    def connectionExpr(self, ast):
        return ast

    def patternSpec(self, ast):
        return ast

    def patternExpr(self, ast):
        return ast

    def term(self, ast):
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
    parser = a4smedlParser(parseinfo=False)
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
    ast = generic_main(main, a4smedlParser, name='a4smedl')
    print('AST:')
    print(ast)
    print()
    print('JSON:')
    print(json.dumps(ast, indent=2))
    print()
