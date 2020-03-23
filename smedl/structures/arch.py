"""
Structures and types for monitoring system architectures (.a4smedl files)
"""

class DeclaredMonitor(object):
    """A monitor delcaration from the architecture file"""
    def __init__(self, name, target, params):
        # Name of the monitor given in the declaration (meaning the "as" name,
        # if provided)
        self.name = name
        # Name of the smedl specification to use for this monitor
        self.target = target
        # List of the parameter types to use for this monitor (as strings)
        self.params = params

    def __repr__(self):
        return "monitor {}({}) as {}".format(
                self.target,
                ", ".join(self.params),
                self.name)
