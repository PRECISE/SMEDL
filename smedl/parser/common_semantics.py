"""
Semantic actions in common between SMEDL and architecture files
"""

from smedl.structures import expr

class CommonSemantics(object):
    """Semantic actions for both SMEDL and architecture files, such as
    converting types to SmedlType."""
    def type(self, ast):
        """Convert type string to a SmedlType"""
        return expr.SmedlType(ast)

    def _default(self, ast):
        """Default case: Return AST as-is"""
        return ast
