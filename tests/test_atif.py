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
        channel.queue_bind(exchange=c.rabbitmq.ctrl_exchange, queue=queue_name)
        
        def callback(ch, method, properties, body):
            global test_step
            body = str(body, 'utf-8')
            if test_step == 0 and body.startswith("Ratecomputation monitor") and body.endswith("started."):
                test_step += 1
        # channel.basic_publish(exchange=c.rabbitmq.ctrl_exchange,
        #     routing_key='', body='Hello World!')
        # time.sleep(1)
        # def callback(ch, method, properties, body):
        #     print(" [x] %r" % body)
        #
        # channel.basic_consume(callback,
        #                       queue=queue_name,
        #                       no_ack=True)
        #
        # channel.start_consuming()
        channel.basic_consume(callback, queue=queue_name, no_ack=True)
        recieve_thread = threading.Thread(target=channel.start_consuming)
        recieve_thread.start()
        if connection is None:
            self.fail()
        call = subprocess.Popen("../bin/stringRate", shell=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        time.sleep(1)
        call.terminate()
        self.terminate_thread(recieve_thread)
        self.assertEqual(1, test_step)

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
