"""
Architecture file semantic actions
"""
from structures import DeclaredMonitor
from grako.exceptions import FailedSemantics

class A4smedlSemantics(object):
    """Semantic actions for A4SMEDL parsing"""
    #def __init__(self, name):
    #    self.__name = name

    def __init__(self):
        # Monitor specifications from .smedl files. Key is name from file. Value
        # is parsed monitor.
        monitor_specs = dict()
        # Declared monitors in the architecture file. Key is the name given in
        # the declaration, value is

    def import_stmt(self, ast):
        """Parse the named SMEDL file"""
        # Strip the opening and closing quotes
        filename = ast[1:-1]
        #TODO parse
        pass

    def monitor_decl(self, ast):
        pass

    def syncset_decl(self, ast):
        pass
