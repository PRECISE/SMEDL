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

class RabbitMQSession:
    """Manages sending and receiving RabbitMQ messages for
    test_monitor_rabbitmq()"""
    def __init__(self, rabbitmq_config, binding_keys, messages):
        """Execute a RabbitMQ session

        rabbitmq_config - A dict with the following keys:
          - 'server'
          - 'port'
          - 'username'
          - 'password'
          - 'exchange'
          - 'vhost'
        binding_keys - A list of binding_keys to bind to
        messages - A list of messages (routing_key, body) to send
        """
        self.config = rabbitmq_config
        self.binding_keys = binding_keys
        self.bound_count = 0
        self.to_send = messages
        self.received = []

        # Initiate connection
        credentials = pika.PlainCredentials(rabbitmq_config['username'],
                                            rabbitmq_config['password'])
        parameters = pika.ConnectionParameters(
            host=rabbitmq_config['server'], port=rabbitmq_config['port'],
            virtual_host=rabbitmq_config['vhost'], credentials=credentials)
        print("@@@ initializing connection")
        self.connection = pika.SelectConnection(
            parameters, on_open_callback=lambda c: self._on_open(c))

        # Do producing and consuming
        try:
            print("@@@ starting")
            self.connection.ioloop.start()
            print("@@@ normal exit")
        except KeyboardInterrupt:
            # This probably won't normally happen, but if tests are run manually
            # Close gracefully
            print("@@@ closing after interrupt")
            self.connection.close()
            # Let Pika handle any remaining communications
            print("@@@ waiting for cleanup messages")
            self.connection.ioloop.start()

        print("@@@ rabbitmq done")

    def _on_open(self, connection):
        print("@@@ conn open")
        connection.channel(on_open_callback=lambda c: self._on_channel(c))

    def _on_channel(self, channel):
        print("@@@ channel open")
        self.channel = channel
        # Declare queue
        channel.queue_declare(
            '', exclusive=True, callback=lambda q: self._on_queue(q))

    def _on_queue(queue):
        self.queue = queue.name
        # Bind to the binding keys for outgoing messages
        print("@@@ queue declared")
        for binding_key in self.binding_keys:
            self.channel.queue_bind(
                exchange=self.config['exchange'], queue=self.queue,
                routing_key=binding_key, callback=lambda b: self._on_bind(b))

    def _on_bind(bind_ok):
        self.bound_count += 1
        print("@@@ queue {} bound".format(self.bound_count))

        if self.bound_count == len(self.binding_keys):
            # Start consuming
            self.channel.basic_consume(
                queue=self.queue, auto_ack=True,
                on_message_callback=lambda c, m, p, b:
                    self._consume(c, m, p, b),
                callback=lambda c: self._produce(consume_ok))

    def _consume(channel, method, properties, body):
        print("@@@ consumed message")
        ev_json = json.loads(body)
        self.received.append((method.routing_key, ev_json))

    def _produce(consume_ok):
        print("@@@ started consuming")

        # Publish messages
        properties = pika.BasicProperties(content_type='application/json',
                                          type='smedl-fmt2.0')
        for rk, body in self.to_send:
            print("@@@ publishing message")
            self.channel.basic_publish(
                exchange=self.config['exchange'], routing_key=rk,
                body=body, properties=properties)
            time.sleep(0.5)

        # Wait a moment for responses
        print("@@@ waiting for last responses")
        time.sleep(2)
        self.connection.close()
        print("@@@ closed")

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

    # Send and receive messages via RabbitMQ
    session = RabbitMQSession(rabbitmq_config, binding_keys, input_events)

    # Terminate monitors
    gen_mon.terminate(5)
    print("@@@ terminated")

    # Check exit statuses
    exit_codes = gen_mon.wait()
    expected_exit_codes = [0] * len(exit_codes)
    assert exit_codes == expected_exit_codes, \
        'Monitors did not all terminate cleanly'

    # Check output messages
    actual_events = session.received
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
