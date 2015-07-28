"""
The SMEDL semantics.
"""

from grako.exceptions import FailedSemantics

keywords = set([
    'object', 'identity', 'opaque', 'state',
    'events', 'imported', 'exported', 'error', 'scenarios',
    'this', 'else', 'raise', 'atomic',
    'when'])


class SmedlSemantics(object):

    def __init__(self, name):
        self.__name = name

    def identifier(self, ast):
        if ast in keywords:
            raise FailedSemantics('"%s" is a keyword' % str(ast))
        return ast

    def _default(self, ast):
        return ast
