"""
Test generated monitors using the file transport. 
"""

import pytest

import sys
import os
import os.path

import smedl
from smedl.parser.exceptions import SmedlException

from utils import *

# List of monitors with test cases
test_monitors = os.listdir(os.path.join(sys.path[0], 'file'))
# List of test case tuples
test_cases = []
for mon in test_monitors:
    files = os.listdir(os.path.join(sys.path[0], 'file', mon))
    for fname in files:
        root, ext = os.path.splitext(fname)
        if ext == '.in':
            test_cases.append((mon, root))
# List of monitors that should fail to generate
bad_monitors = os.listdir(os.path.join(sys.path[0], 'bad_monitors'))

@pytest.fixture
def generated_file_monitor(request):
    """Fixture to generate a named monitor that's ready to execute"""
    mon = request.param
    mon_path = os.path.join(sys.path[0], 'monitors', mon, mon + '.a4smedl')
    gen_mon = GeneratedMonitor(mon_path, 'file')
    gen_mon.build()
    return gen_mon

@pytest.mark.parametrize('generated_file_monitor, test_case', test_cases,
        indirect=['generated_file_monitor'], scope='module')
def test_monitor(generated_file_monitor, test_case):
    """Test the given monitor with the named testcase"""
    path = os.path.join(sys.path[0], 'file', generated_file_monitor.fname)
    with open(os.path.join(path, test_case + '.in'), 'r') as f:
        stdin = f.read()
    with open(os.path.join(path, test_case + '.out'), 'r') as f:
        expected = f.read()

    generated_file_monitor.run(capture_output=True)
    stdout, stderr = generated_file_monitor.communicate([stdin], timeout=15)[0]
    print(stderr, file=sys.stderr)

    actual_json = parse_multiple_json(stdout)
    expected_json = parse_multiple_json(expected)
    assert actual_json == expected_json, \
            'Output messages did not match expected'
    #assert stderr == ''

@pytest.mark.parametrize('generated_file_monitor', test_monitors,
        indirect=True)
def test_file_names(generated_file_monitor):
    """Test that generated file names are correct for the named monitor"""
    # Fetch all names
    sys_name = generated_file_monitor.system.name
    syncsets = generated_file_monitor.system.syncsets.keys()
    mon_names = generated_file_monitor.system.monitor_decls.keys()
    spec_names = [decl.spec.name for decl in
            generated_file_monitor.system.monitor_decls.values()]

    # Get a list of all the file names in the temp dir
    files = os.listdir(generated_file_monitor.gen_dir)

    # Check that all the expected files are present
    assert sys_name in files
    assert sys_name + "_file.c" in files
    assert sys_name + "_file.h" in files
    for syncset in syncsets:
        assert syncset + "_global_wrapper.c" in files
        assert syncset + "_global_wrapper.h" in files
    for mon in mon_names:
        assert mon + "_local_wrapper.c" in files
        assert mon + "_local_wrapper.h" in files
    for spec in spec_names:
        assert mon + "_mon.c" in files
        assert mon + "_mon.h" in files

@pytest.mark.parametrize('mon', bad_monitors)
def test_invalid_monitor(tmp_path, mon):
    """Test that generation of the named monitor fails

    tmp_path - The tmp_path fixture
    mon - The name of a directory under bad_monitors/
    """
    mon_path = os.path.join(sys.path[0], 'monitors', mon, mon + '.a4smedl')
    generator = smedl.MonitorGenerator(out_dir=tmp_path)
    with pytest.raises(SmedlException):
        generator.generate(mon_path)
