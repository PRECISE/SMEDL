import unittest
import subprocess
import os
import time
import threading
import ctypes
import pathlib
import pika
import pylibconfig2 as cfg

test_step = 0

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
        os.makedirs('bin', exist_ok=True)
        call = subprocess.run("make all", shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(0, call.returncode)

    def test_atif_run(self):
        global test_step
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
        channel.queue_bind(exchange=c.rabbitmq.ctrl_exchange, queue=queue_name,routing_key='#')

        channel1 = connection.channel()
        channel1.exchange_declare(exchange=c.rabbitmq.exchange, exchange_type='topic', durable=True)
        result1 = channel1.queue_declare(exclusive=True)
        queue_name1 = result1.method.queue
        channel1.queue_bind(exchange=c.rabbitmq.exchange, queue=queue_name1,routing_key='ch2.#')

        def callback(ch, method, properties, body):
            global test_step
            body = str(body, 'utf-8')
            print(body)
            if test_step == 0:
                test_step += 1
            if test_step == 1:
                test_step += 1
                channel.basic_publish(exchange=c.rabbitmq.exchange,
                routing_key='ch3.foo', body="{\"name\":\"0\", \"fmt_version\":\"1.0.0\", \"params\":{\"v1\": \"0\", \"v2\":1.0, \"v3\":0}}")
                channel.basic_publish(exchange=c.rabbitmq.exchange,
                routing_key='ch3.foo', body="{\"name\":\"0\", \"fmt_version\":\"1.0.0\",\"params\":{\"v1\": \"0\", \"v2\":2.0, \"v3\":1000}}")
                channel.basic_publish(exchange=c.rabbitmq.exchange,
                routing_key='ch3.foo', body="{\"name\":\"0\",\"fmt_version\":\"1.0.0\", \"params\":{\"v1\": \"0\", \"v2\":3.0, \"v3\":2000}}")
                channel.basic_publish(exchange=c.rabbitmq.exchange,
                routing_key='ch4.foo', body="{\"name\":\"timeout\",\"fmt_version\":\"1.0.0\"}")
            #elif test_step == 2 and "\"v1\":	\"0\"" in body and "\"v2\":	3" in body and "\"v3\":	1500" in body:
            elif test_step == 2:
                test_step += 1
            elif test_step == 3 and "thresholdcrossdetection_thresholdWarning" in body:
                test_step += 1

        channel.basic_consume(callback, queue=queue_name, no_ack=True)
        recieve_thread = threading.Thread(target=channel.start_consuming)
        recieve_thread.start()

        channel1.basic_consume(callback, queue=queue_name1, no_ack=True)
        recieve_thread1 = threading.Thread(target=channel1.start_consuming)
        recieve_thread1.start()

        if connection is None:
            self.fail()

        call = subprocess.Popen("../bin/stringRate", shell=True,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        call2 = subprocess.Popen("../bin/stringThresh", shell=True,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        call3 = subprocess.Popen("../bin/adaptationTrigger", shell=True,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        time.sleep(5)
        call.terminate()
        call2.terminate()
        call3.terminate()
        self.terminate_thread(recieve_thread)
        self.terminate_thread(recieve_thread1)
        self.assertEqual(4, test_step)


    def terminate_thread(self, thread):
        """Terminates a python thread from another thread.

        :param thread: a threading.Thread instance
        """
        if not thread.isAlive():
            return

        exc = ctypes.py_object(SystemExit)
        res = ctypes.pythonapi.PyThreadState_SetAsyncExc(ctypes.c_long(thread.ident), exc)
        if res == 0:
            raise ValueError("nonexistent thread id")
        elif res > 1:
        # """if it returns a number greater than one, you're in trouble,
        # and you should call it again with exc=NULL to revert the effect"""
            ctypes.pythonapi.PyThreadState_SetAsyncExc(thread.ident, None)
            raise SystemError("PyThreadState_SetAsyncExc failed")

if __name__ == '__main__':
    unittest.main()
