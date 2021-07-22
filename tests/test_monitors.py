"""
Test generated monitors using the RabbitMQ transport.
"""

import pytest

import sys
import os
import os.path

import smedl
from smedl.parser.exceptions import SmedlException

from utils import *

# Gather test cases
test_monitors, test_cases = collect_test_cases()
# List of monitors that should fail to generate
bad_monitors = os.listdir(os.path.join(sys.path[0], 'bad_monitors'))

@pytest.fixture(scope='module')
def generated_monitor(request, rabbitmq_config):
    """Fixture to generate a named monitor that's ready to execute"""
    mon = request.param
    mon_path = os.path.join(sys.path[0], 'monitors', mon, mon + '.a4smedl')
    gen_mon = GeneratedMonitor(mon_path, 'rabbitmq')
    build_dir = gen_mon.build()

    # Generate config (defaults for all but 'exchange' are in conftest.py
    if rabbitmq_config['exchange'] is None:
        rabbitmq_config['exchange'] = 'smedl.' + gen_mon.system.name
    config_path = os.path.join(build_dir, gen_mon.system.name + '.cfg')
    with open(config_path, 'w') as f:
        json.dump(rabbitmq_config, f)

    # Could return rabbitmq_config as well if that turns out to be useful to
    # some tests
    return gen_mon

@pytest.mark.parametrize('generated_monitor, test_case, input_execs',
        test_cases, indirect=['generated_monitor'], scope='module')
def test_monitor(generated_monitor, test_case, input_execs):
    """Test the given monitor with the named testcase"""
    # Load stdins from .in files and expected outputs from .out files
    path = os.path.join(sys.path[0], 'monitors', generated_monitor.fname)
    stdins = dict()
    expecteds = dict()
    for input_exec in input_execs:
        with open(os.path.join(path,
                               f'{test_case}.{input_exec}.in'),
                               'r') as f:
            stdin = f.read()
            stdins[input_exec] = stdin
        with open(os.path.join(path,
                               f'{test_case}.{input_exec}.out'),
                               'r') as f:
            expected = f.read()
            expecteds[input_exec] = expected

    # Run monitors
    stdouts, stderrs = generated_monitor.run(stdins, timeout=15)
    for exec_name, stderr in stderrs.keys():
        if len(stderr) > 0:
            print(f'***** STDERR for {exec_name} *****', file=sys.stderr)
            print(stderr, file=sys.stderr)

    # Verify results
    for exec_name, stdout in stdouts:
        if exec_name in expecteds:
            assert stdout.splitlines() == expecteds[exec_name].splitlines(), \
                f'Output events for {exec_name} did not match expected'
        else:
            assert stdout.splitlines() == [], \
                f'Output events for {exec_name} were not empty as expected'

@pytest.mark.parametrize('generated_monitor', test_monitors, indirect=True)
def test_file_names(generated_monitor):
    """Test that generated file names are correct for the named monitor"""
    # Fetch all names
    sys_name = generated_monitor.system.name
    syncsets = generated_monitor.system.syncsets.keys()
    mon_names = generated_monitor.system.monitor_decls.keys()
    spec_names = [decl.spec.name for decl in
            generated_monitor.system.monitor_decls.values()]

    # Get a list of all the file names in the temp dir
    files = os.listdir(generated_monitor.gen_dir)

    # Check that all the expected files are present
    assert f"{sys_name}.cfg" in files
    assert f"{sys_name}_defs.h" in files
    for syncset in syncsets:
        assert syncset in files
        assert f"{syncset}_manager.c" in files
        assert f"{syncset}_manager.h" in files
        assert f"{syncset}_global_wrapper.c" in files
        assert f"{syncset}_global_wrapper.h" in files
        assert f"{syncset}_rabbitmq.c" in files
        assert f"{syncset}_rabbitmq.h" in files
        if generated_monitor.system.syncsets[syncset].pure_async:
            assert f"{syncset}_stub.c" not in files
            assert f"{syncset}_stub.h" not in files
        else:
            assert f"{syncset}_stub.c" in files
            assert f"{syncset}_stub.h" in files
    for mon in mon_names:
        assert f"{mon}_local_wrapper.c" in files
        assert f"{mon}_local_wrapper.h" in files
    for spec in spec_names:
        assert f"{spec}_mon.c" in files
        assert f"{spec}_mon.h" in files

@pytest.mark.parametrize('mon', bad_monitors)
def test_invalid_monitor(tmp_path, mon):
    """Test that generation of the named monitor fails

    tmp_path - The tmp_path fixture
    mon - The name of a directory under bad_monitors/
    """
    mon_path = os.path.join(sys.path[0], 'bad_monitors', mon, mon + '.a4smedl')
    generator = smedl.MonitorGenerator(out_dir=tmp_path)
    with pytest.raises(SmedlException):
        generator.generate(mon_path)
