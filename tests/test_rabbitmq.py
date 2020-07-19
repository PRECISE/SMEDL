"""
Test generated monitors using the file transport. 
"""

import pytest

import sys
import os
import os.path
import time
import json

import pika

import smedl
from smedl.parser.exceptions import SmedlException

from utils import *

# Gather test cases
test_monitors, test_cases = collect_test_cases()

@pytest.fixture(scope='module')
def generated_rabbitmq_monitor(request, rabbitmq_config):
    """Fixture to generate a named monitor that's ready to execute"""
    mon = request.param
    mon_path = os.path.join(sys.path[0], 'monitors', mon, mon + '.a4smedl')
    gen_mon = GeneratedMonitor(mon_path, 'rabbitmq')
    build_dir = gen_mon.build()
    
    # Generate config
    if rabbitmq_config['exchange'] is None:
        rabbitmq_config['exchange'] = 'smedl.' + gen_mon.system.name
    config_path = os.path.join(build_dir, gen_mon.system.name + '.cfg')
    with open(config_path, 'w') as f:
        json.dump(rabbitmq_config, f)

    return gen_mon, rabbitmq_config

def text_to_message_iterator(text):
    """Convert a flat file with the input test cases into an iterator of tuples
    (routing key, body) where body is parsed json with the structure the
    RabbitMQ SMEDL adapter needs"""
    parsed_text = parse_multiple_json(text)
    for event in parsed_text:
        rk = event['channel'] + '.' + event['event']
        del event['fmt_version']
        del event['channel']
        yield (rk, event)

@pytest.mark.parametrize('generated_rabbitmq_monitor, test_case', test_cases,
        indirect=['generated_rabbitmq_monitor'], scope='module')
def test_monitor_rabbitmq(generated_rabbitmq_monitor, test_case):
    """Test the given monitor with the named testcase using RebbitMQ"""
    gen_mon, rabbitmq_config = generated_rabbitmq_monitor

    # Read in test data
    path = os.path.join(sys.path[0], 'monitors', gen_mon.fname)
    with open(os.path.join(path, test_case + '.in'), 'r') as f:
        input_text = f.read()
    with open(os.path.join(path, test_case + '.out'), 'r') as f:
        expected_text = f.read()
    with open(os.path.join(path, 'testinfo.json'), 'r') as f:
        testinfo = json.load(f)

    # Transform test data
    # input_events is list of (rk, string_body)
    input_events = [(rk, json.dumps(body)) for rk, body in
                    text_to_message_iterator(input_text)]
    # expected_events is list of (rk, parsed_body)
    expected_events = list(text_to_message_iterator(expected_text))
    # binding_keys is a list of strings
    binding_keys = []
    for ev in testinfo['output_events']:
        ev = ev.split('.')
        binding_keys.append('_%s_%s.#' % (ev[0], ev[1]))

    # Start monitors
    gen_mon.run(capture_output=False)

    # Prepare RabbitMQ callbacks - One to receive messages, one to subscribe
    # then publish messages
    actual_events = []
    def consume(channel, method, properties, body):
        ev_json = json.loads(body)
        actual_events.append((method.routing_key, ev_json))
    def produce(channel):
        # Declare queue
        queue = channel.queue_declare('', exclusive=True)

        # Bind to the binding keys for outgoing messages
        for binding_key in binding_keys:
            channel.queue_bind(exchange=rabbitmq_config['exchange'],
                               queue=queue.method.name,
                               routing_key=binding_key)

        # Start consuming
        channel.basic_consume(queue=queue.method.name, auto_ack=True,
                              on_message_callback=consume)

        # Publish messages
        properties = pika.BasicProperties(content_type='application/json',
                                          type='smedl-fmt2.0')
        for rk, body in input_events:
            channel.basic_publish(exchange=rabbitmq_config['exchange'],
                                  routing_key=rk, body=body,
                                  properties=properties)

        # Wait a moment for responses
        time.sleep(2)
        connection.close()

    # Set up connection and channel to RabbitMQ server
    credentials = pika.PlainCredentials(rabbitmq_config['username'],
                                        rabbitmq_config['password'])
    parameters = pika.ConnectionParameters(
        host=rabbitmq_config['server'], port=rabbitmq_config['port'],
        virtual_host=rabbitmq_config['vhost'], credentials=credentials)
    def on_open(conection):
        connection.channel(on_open_callback=produce)
    connection = pika.SelectConnection(parameters, on_open_callback=on_open)

    # Do producing and consuming
    try:
        connection.ioloop.start()
    except KeyboardInterrupt:
        # This probably won't normally happen, but if tests are run manually
        # Close gracefully
        connection.close()
        # Let Pika handle any remaining communications
        connection.ioloop.start()

    # Terminate monitors
    gen_mon.terminate(5)

    # Check exit statuses
    exit_codes = gen_mon.wait()
    expected_exit_codes = [0] * len(exit_codes)
    assert exit_codes == expected_exit_codes, \
        'Monitors did not all terminate cleanly'

    assert actual_events == expected_events, \
        'Output messages did not match expected'

@pytest.mark.parametrize('generated_rabbitmq_monitor', test_monitors,
        indirect=True)
def test_rabbitmq_names(generated_rabbitmq_monitor):
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
    assert sys_name + ".cfg" in files
    for syncset in syncsets:
        assert syncset in files
        assert syncset + "_global_wrapper.c" in files
        assert syncset + "_global_wrapper.h" in files
        assert syncset + "_rabbitmq.c" in files
        assert syncset + "_rabbitmq.h" in files
    for mon in mon_names:
        assert mon + "_local_wrapper.c" in files
        assert mon + "_local_wrapper.h" in files
    for spec in spec_names:
        assert mon + "_mon.c" in files
        assert mon + "_mon.h" in files
