import sys

# This is to prevent importing SMEDL from failing in code which can only be run
# in Python 2.7, ex. LLDB-dependent code
if sys.version_info > (3, 0):
    from .mgen import MonitorGenerator

    __all__ = [
        'MonitorGenerator'
    ]
