"""
Python module for C unit tests
"""

CC='cc'
CPPFLAGS=[]
CFLAGS=['std=c99']
LDFLAGS=[]
LDLIBS=[]

import pytest

import os
import os.path
import subprocess

# importlib.resources is only available in python>=3.7, but is available as a
# backport.
try:
    from importlib import resources
except ImportError:
    import importlib_resources as resources

def copy_resources(module, dest, res_list=None):
    """Copy resources from the given module to the given destination, a string
    or path-like object. If a res_list is given, copy only those resources (if
    they exist), otherwise copy all resources except __init__.py. Return a list
    of copied files."""
    result = []
    if res_list is None:
        files = resources.contents(module)
    else:
        files = res_list
    for f in files:
        if f == '__init__.py':
            continue
        elif resources.is_resource(module, f):
            result.append(f)
            out_path = os.path.join(dest, f)
            text = resources.read_text(module, f)
            with open(out_path, "w") as outfile:
                outfile.write(text)
    return result

def gather_tests(dest):
    """Gather a list of tests as follows:
    1) Find all the test_*.c files in the given directory
    2) Find the matching *.c file (same name but without "test_")
    3) Create a tuple with those two and "unity.c"
    4) Return a list of all such tuples
    """
    result = []
    files = os.listdir(dest)
    for fname in files:
        root, ext = os.path.splitext(fname)
        if root[:5] == 'test_' and ext == '.c' and fname[5:] in files:
            result.append((fname, fname[5:], 'unity.c'))
    return result

def test_c_units_main(tmp_path):
    """Test C units for the main static files (smedl_types.c, monitor_map.c,
    etc.)"""
    import ctests
    from smedl.codegen import static
    copy_resources(ctests, tmp_path)
    copy_resources(static, tmp_path)

    # Build unit tests
    c_files = gather_c_files(tmp_path)
    subprocess.run(CC, *CPPFLAGS, *CFLAGS, *LDFLAGS, *c_files, *LDLIBS,
            '-o', 'main.out', check=True)


