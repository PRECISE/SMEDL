"""
Python module for C unit tests
"""

build_vars = {
    'CC': 'cc'
    'CPPFLAGS': []
    'CFLAGS': ['std=c99']
    'LDFLAGS': []
    'LDLIBS': []
}

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

def gather_tests(module):
    """Gather a list of tests as follows:
    1) Find all the test_*.c resources in the given module
    2) Create a tuple with that, the target file (same name but without
       "test_"), and "unity.c"
    3) Return a list of all such tuples
    """
    result = []
    files = resources.contents(module)
    for fname in files:
        if resources.is_resource(module, fname):
            root, ext = os.path.splitext(fname)
            if root[:5] == 'test_' and ext == '.c':
                result.append((fname, fname[5:], 'unity.c'))
    return result

def parse_unity_results(output):
    """Read output from Unity and parse the results into 5-tuples:
    (file, lineno, name, result, message)"""
    result = []
    lines = output.split('\n')
    for line in lines:
        if line == '':
            break
        parts = line.split(':')
        if len(parts) == 4:
            parts.append(None)
        else:
            parts[5] = parts[5][1:]
        result.append(tuple(parts))
    return result

def build_and_run_tests(cwd, c_files, CC='cc', CPPFLAGS=[], CFLAGS=[],
        LDFLAGS=[], LDLIBS=[]):`
    """Build unit tests from the named C files, with the given build options,
    in the given directory. Run the tests and verify the results."""
    # Build unit tests
    subprocess.run(CC, *CPPFLAGS, *CFLAGS, *LDFLAGS, *c_files, *LDLIBS,
            '-o', 'test.out', cwd=cwd, check=True)

    # Run unit tests
    result = subprocess.run('./test.out', cwd=cwd, capture_output=True,
            universal_newlines=True)

    assert result.returncode >= 0, 'Unit tests terminated by signal'

    for test in parse_unity_results(result.stdout):
        msg = 'Test {} ({}:{}) failed: {}'.format(test[2], test[0], test[1],
                test[4])
        assert test[3] != 'FAIL', msg

from ctests import unity

import ctests
from smedl.codegen import static

@pytest.fixture(scope='module')
def tmp_common(tmp_path):
    """Prepare a temp dir with all the sources for common static file tests"""
    copy_resources(ctests, tmp_path)
    copy_resources(static, tmp_path)
    copy_resources(unity, tmp_path)
    yield tmp_path

@pytest.mark.parameterize('c_files', gather_tests(ctests))
def test_c_units_common(tmp_common, c_files):
    """Test C units for the common static files (smedl_types.c, monitor_map.c,
    etc.)"""
    build_and_run_tests(tmp_common, c_files, **build_vars)

#TODO add fixture and test func for file, rabbitmq
