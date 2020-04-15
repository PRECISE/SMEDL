import sys
import json
import pkg_resources
import codecs

# Get the package details from the SMEDL about.json file
io = pkg_resources.resource_stream(__name__, "about.json")
utf8_reader = codecs.getreader("utf-8")
__about__ = json.load(utf8_reader(io))

from .mgen import MonitorGenerator

__all__ = [
    'MonitorGenerator'
]
