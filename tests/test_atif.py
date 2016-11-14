import unittest
import subprocess
import os
import pathlib
import pika
import pylibconfig2 as cfg

class TestAtif(unittest.TestCase):

    def setUp(self):
        self.origPath = os.getcwd()

    def tearDown(self):
        os.chdir(self.origPath)

    def test_atif_mgen(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/atif/smedl/stringRate","--arch=tests/examples/atif/smedl/atifMonitorArchString","--helper","helper.h"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_atif_mgen1(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/atif/smedl/stringThresh","--arch=tests/examples/atif/smedl/atifMonitorArchString","--helper","helper.h"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_atif_mgen2(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/atif/smedl/adaptationTrigger","--arch=tests/examples/atif/smedl/atifMonitorArchString","--helper","helper.h"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    
    def test_atif_compile(self):
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'atif')))
        call = subprocess.run("make all", shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(0, call.returncode)

    def test_atif_run(self):
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'atif','cfg')))
        with open('stringRate_mon.cfg', 'r') as cfgfile:
            cfgdata = cfgfile.read()
        c = cfg.Config(cfgdata)
        credentials = pika.PlainCredentials(c.rabbitmq.username, c.rabbitmq.password)
        try:
            connection = pika.BlockingConnection(pika.ConnectionParameters(
                c.rabbitmq.hostname, c.rabbitmq.port, '/', credentials))
        except pika.exceptions.ConnectionClosed:
            self.fail("Could not connect to RabbitMQ server. Is it down?")
        channel = connection.channel()
        channel.exchange_declare(exchange=c.rabbitmq.ctrl_exchange, exchange_type='fanout', durable=True)
        result = channel.queue_declare(exclusive=True)
        queue_name = result.method.queue
        channel.queue_bind(exchange=c.rabbitmq.ctrl_exchange, queue=queue_name)

        # def callback(ch, method, properties, body):
        #     print(" [x] %r" % body)
        #
        # channel.basic_consume(callback,
        #                       queue=queue_name,
        #                       no_ack=True)
        #
        # channel.start_consuming()

        if connection is None:
            self.fail()
        call = subprocess.Popen("bin/stringRate")
        #TODO if channel.received("smedl.control") startswith "Spv monitor" and endswith "started."
        call.terminate()


if __name__ == '__main__':
    unittest.main()
