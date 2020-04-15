import json

# importlib.resources is only available in python>=3.7, but is available as a
# backport.
try:
    from importlib import resources
except ImportError:
    import importlib_resources as resources

# Get the package details from the SMEDL about.json file
about_stream = resources.open_text(__name__, 'about.json')
__about__ = json.load(about_stream)

from .mgen import MonitorGenerator

__all__ = [
    'MonitorGenerator'
]
