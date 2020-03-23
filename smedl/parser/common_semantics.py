"""
Semantic actions in common between SMEDL and architecture files
"""

import structures

class CommonSemantics(object):
    """Semantic actions for both SMEDL and architecture files, such as
    converting types to SmedlType."""
    def type(self, ast):
        return structures.SmedlType(ast)
