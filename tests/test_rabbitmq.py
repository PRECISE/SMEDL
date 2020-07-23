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
          - 'hostname'
          - 'port'
          - 'username'
          - 'password'
          - 'exchange'
          - 'vhost'
        binding_keys - A list of binding keys to bind to
        messages - A list of messages (routing_key, body) to send
        """
        self.config = rabbitmq_config
        self.binding_keys = binding_keys
        self.bound_count = 0
        self.to_send = messages
        self.sent_count = 0
        self.received = []

    def run(self):
        # Initiate connection
        credentials = pika.PlainCredentials(self.config['username'],
                                            self.config['password'])
        parameters = pika.ConnectionParameters(
            host=self.config['hostname'], port=self.config['port'],
            virtual_host=self.config['vhost'], credentials=credentials)
        #print("@@@ initializing connection")
        #print("@@@ config", self.config)
        self.connection = pika.BlockingConnection(parameters)

        #TODO Figure out how to make sure this doesn't happen until the
        # exchange is declared. This try/retry thing isn't working.
        try:
            self._setup_channel()
            retry = False
        except pika.exceptions.ChannelClosedByBroker:
            retry = True
        if retry:
            time.sleep(1)
            self._setup_channel()
        self._setup_queue()
        self._start()

        try:
            #print("@@@ starting")
            self.channel.start_consuming()
            #print("@@@ rabbitmq done")
        except KeyboardInterrupt:
            # This probably won't normally happen, but if tests are run manually
            # Close gracefully
            #print("@@@ closing after interrupt")
            self.connection.call_later(0, self._finish)
            # Let Pika handle any remaining communications
            #print("@@@ waiting for cleanup messages")
            self.channel.start_consuming()

    def _setup_channel(self):
        #print("@@@ opening channel")
        self.channel = self.connection.channel()
        #print("@@@ declaring exchange")
        # This should not be necessary. The monitor will declare the exchange.
        # But if the monitor dies early, the Pika exception from the missing
        # exchange will end the test early and keep us from seeing the exit
        # status for the monitor (which is the best indication if e.g. a
        # segmentation fault killed it).
        self.channel.exchange_declare(
            exchange=self.config['exchange'], exchange_type='topic',
            passive=True)
            #auto_delete=True)

    def _setup_queue(self):
        #print("@@@ declaring queue")
        result = self.channel.queue_declare('', exclusive=True)
        self.queue = result.method.queue
        #print("@@@ binding queue")
        for binding_key in self.binding_keys:
            #print("@@@ rk:", binding_key)
            self.channel.queue_bind(
                exchange=self.config['exchange'], queue=self.queue,
                routing_key=binding_key)

    def _start(self):
        #print("@@@ starting basic consume")
        self.channel.basic_consume(queue=self.queue, auto_ack=True,
                                   on_message_callback=self._consume)
        self.connection.call_later(0, self._publish)

    def _consume(self, channel, method, properties, body):
        #print("@@@ consumed message:", method.routing_key)
        print(body)
        ev_json = json.loads(body)
        self.received.append((method.routing_key, ev_json))

    def _publish(self):
        try:
            rk, body = self.to_send[self.sent_count]
            self.sent_count += 1
        except IndexError:
            #print("@@@ waiting for last responses")
            self.connection.call_later(1.5, self._finish)
            return

        properties = pika.BasicProperties(content_type='application/json',
                                          type='smedl-fmt2.0')
        #print("@@@ publishing message:", rk)
        print(body)
        self.channel.basic_publish(
            exchange=self.config['exchange'], routing_key=rk,
            body=body, properties=properties)
        self.connection.call_later(0.5, self._publish)

    def _finish(self):
        #print("@@@ closing connection")
        self.connection.close()

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
    session.run()

    # Terminate monitors
    gen_mon.terminate(5)

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
    gen_mon, _ = generated_rabbitmq_monitor
    # Fetch all names
    sys_name = gen_mon.system.name
    syncsets = gen_mon.system.syncsets.keys()
    mon_names = gen_mon.system.monitor_decls.keys()
    spec_names = [decl.spec.name for decl in
            gen_mon.system.monitor_decls.values()]

    # Get a list of all the file names in the temp dir
    files = os.listdir(gen_mon.gen_dir)

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
