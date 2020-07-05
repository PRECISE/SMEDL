import unittest
import subprocess
import os
import time
import threading
import ctypes
import pathlib
import pika
import libconf

test_step = 0

class TestProvenance(unittest.TestCase):

    def setUp(self):
        self.origPath = os.getcwd()

    def tearDown(self):
        os.chdir(self.origPath)

    def test_provenance_mgen(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/provenance/smedl/stringRate","--arch=tests/examples/provenance/smedl/atifMonitorArchString","--helper","helper.h"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_provenance_mgen1(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/provenance/smedl/stringThresh","--arch=tests/examples/provenance/smedl/atifMonitorArchString","--helper","helper.h"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_provenance_mgen2(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/provenance/smedl/adaptationTrigger","--arch=tests/examples/provenance/smedl/atifMonitorArchString","--helper","helper.h"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_provenance_compile(self):
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'provenance')))
        os.makedirs('bin', exist_ok=True)
        call = subprocess.run("make all", shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(0, call.returncode)

    def test_provenance_run(self):
        global test_step
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'provenance','cfg')))
        with open('stringRate_mon.cfg', 'r') as cfgfile:
            cfg = libconf.load(cfgfile)
        credentials = pika.PlainCredentials(cfg['rabbitmq']['username'], cfg['rabbitmq']['password'])
        try:
            connection = pika.BlockingConnection(pika.ConnectionParameters(
                cfg['rabbitmq']['hostname'], cfg['rabbitmq']['port'], '/', credentials))
        except pika.exceptions.ConnectionClosed:
            self.fail("Could not connect to RabbitMQ server. Is it down?")

        channel = connection.channel()
        channel.exchange_declare(exchange=cfg['rabbitmq']['ctrl_exchange'], exchange_type='fanout', durable=True)
        result = channel.queue_declare(exclusive=True)
        queue_name = result.method.queue
        channel.queue_bind(exchange=cfg['rabbitmq']['ctrl_exchange'], queue=queue_name,routing_key='#')

        channel1 = connection.channel()
        channel1.exchange_declare(exchange=cfg['rabbitmq']['exchange'], exchange_type='topic', durable=True)
        result1 = channel1.queue_declare(exclusive=True)
        queue_name1 = result1.method.queue
        channel1.queue_bind(exchange=cfg['rabbitmq']['exchange'], queue=queue_name1,routing_key='ch2.#')

        def callback(ch, method, properties, body):
            global test_step
            body = str(body, 'utf-8')
            print(body)
            if test_step == 0:
                test_step += 1
            if test_step == 1:
                test_step += 1
                channel.basic_publish(exchange=cfg['rabbitmq']['exchange'],
                routing_key='ch3.foo', body="{\"name\":\"0\", \"fmt_version\":\"1.0.0\", \"params\":{\"v1\": \"0\", \"v2\":1.0, \"v3\":0}}")
                channel.basic_publish(exchange=cfg['rabbitmq']['exchange'],
                routing_key='ch3.foo', body="{\"name\":\"0\", \"fmt_version\":\"1.0.0\",\"params\":{\"v1\": \"0\", \"v2\":2.0, \"v3\":1000}}")
                channel.basic_publish(exchange=cfg['rabbitmq']['exchange'],
                routing_key='ch3.foo', body="{\"name\":\"0\",\"fmt_version\":\"1.0.0\", \"params\":{\"v1\": \"0\", \"v2\":3.0, \"v3\":2000}}")
                channel.basic_publish(exchange=cfg['rabbitmq']['exchange'],
                routing_key='ch4.foo', body="{\"name\":\"timeout\",\"fmt_version\":\"1.0.0\"},\"provenance\":{\"event\": \"e3\", \"line\":20, \"trace_counter\":2}}")
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

        time.sleep(15)
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