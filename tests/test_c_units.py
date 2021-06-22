"""
Python module for C unit tests
"""

build_vars = {
    'CC': 'cc',
    'CPPFLAGS': ['-DUNITY_INCLUDE_CONFIG_H'],
    'CFLAGS': ['-std=c99'],
    'LDFLAGS': [],
    'LDLIBS': []
}

import pytest

import os
import os.path
import subprocess
import tempfile

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
                result.append(pytest.param(
                    (fname, fname[5:], 'unity.c'),
                    id=fname[5:]
                ))
    return result

def parse_unity_results(output):
    """Read output from Unity and parse the results into 5-tuples:
    (file, lineno, name, result, message)"""
    result = []
    lines = output.split('\n')
    for line in lines:
        if line == '':
            break
        parts = line.split(':', maxsplit=4)
        if len(parts) == 4:
            parts.append(None)
        else:
            parts[4] = parts[4][1:]
        result.append(tuple(parts))
    return result

def build_and_run_tests(cwd, c_files, CC='cc', CPPFLAGS=[], CFLAGS=[],
        LDFLAGS=[], LDLIBS=[], timeout=30):
    """Build unit tests from the named C files, with the given build options,
    in the given directory. Run the tests and verify the results."""
    # Build unit tests
    args = [CC, *CPPFLAGS, *CFLAGS, *LDFLAGS, *c_files, *LDLIBS, '-o',
            'test.out']
    subprocess.run(args, cwd=cwd, check=True)

    # Run unit tests
    # Unity doesn't write to stderr, but redirect to stdout for completeness
    try:
        result = subprocess.run('./test.out', cwd=cwd, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, universal_newlines=True,
                timeout=timeout)
    finally:
        # Print full results for when tests fail and visibility with -v
        print(result.stdout, end='', flush=True)

    assert result.returncode >= 0, 'Unit tests terminated by signal'

    for test in parse_unity_results(result.stdout):
        msg = 'Test {} ({}:{}) failed'.format(test[2], test[0], test[1])
        if test[4] is not None:
            msg += ': {}'.format(test[4])
        assert test[3] != 'FAIL', msg

from ctests import unity

import ctests
from smedl.codegen import static

@pytest.fixture(scope='module')
def tmp_dir_common():
    """Prepare a temp dir with all the sources for common static file tests"""
    tmp_dir = tempfile.TemporaryDirectory()
    copy_resources(ctests, tmp_dir.name)
    copy_resources(static, tmp_dir.name)
    copy_resources(unity, tmp_dir.name)
    yield tmp_dir.name

@pytest.mark.parametrize('c_files', gather_tests(ctests))
def test_c_units_common(tmp_dir_common, c_files):
    """Test C units for the common static files (smedl_types.c, monitor_map.c,
    etc.)"""
    build_and_run_tests(tmp_dir_common, c_files, timeout=15, **build_vars)

# NOTE: No unit tests for the RabbitMQ adapter. There are no static files
# except cJSON, an external library (presumably tested by its developer).

import ctests.file
import smedl.codegen.file.static

@pytest.fixture(scope='module')
def tmp_dir_file():
    """Prepare a temp dir with all the sources for file adapter static file
    tests"""
    tmp_dir = tempfile.TemporaryDirectory()
    copy_resources(ctests.file, tmp_dir.name)
    copy_resources(smedl.codegen.file.static, tmp_dir.name)
    copy_resources(unity, tmp_dir.name)
    yield tmp_dir.name

@pytest.mark.parametrize('c_files', gather_tests(ctests.file))
def test_c_units_file(tmp_dir_file, c_files):
    """Test C units for the file adapter static files"""
    build_and_run_tests(tmp_dir_file, c_files, timeout=15, **build_vars)
