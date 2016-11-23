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

class TestSpv(unittest.TestCase):

    def setUp(self):
        self.origPath = os.getcwd()

    def tearDown(self):
        os.chdir(self.origPath)

    def test_spv_mgen(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "gen",
            "tests/examples/spv/spv",
            "--arch=tests/examples/spv/spv_architecture"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_spv_compile(self):
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'spv')))
        os.makedirs('bin', exist_ok=True)
        call = subprocess.run("make all", shell=True, check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(0, call.returncode)

    def test_spv_run(self):
        global test_step
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'spv')))
        with open('spv_mon.cfg', 'r') as cfgfile:
            cfg = libconf.load(cfgfile)
        credentials = pika.PlainCredentials(cfg['rabbitmq']['username'], cfg['rabbitmq']['password'])
        try:
            connection = pika.BlockingConnection(pika.ConnectionParameters(
                cfg['rabbitmq']['hostname'], cfg['rabbitmq']['port'], '/', credentials))
        except pika.exceptions.ConnectionClosed:
            self.fail("Could not connect to RabbitMQ server. Is it down?")
        channel = connection.channel()
        channel.exchange_declare(exchange=cfg['rabbitmq']['ctrl_exchange'],
            exchange_type='fanout', durable=True)
        result = channel.queue_declare(exclusive=True)
        queue_name = result.method.queue
        channel.queue_bind(exchange=cfg['rabbitmq']['ctrl_exchange'], queue=queue_name)

        def callback(ch, method, properties, body):
            global test_step
            body = str(body, 'utf-8')
            if test_step == 0 and body.startswith("Spv monitor") and body.endswith("started."):
                test_step += 1

        channel.basic_consume(callback, queue=queue_name, no_ack=True)
        recieve_thread = threading.Thread(target=channel.start_consuming)
        recieve_thread.start()
        if connection is None:
            self.fail()
        call = subprocess.Popen("bin/monitor", shell=True,
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
        res = ctypes.pythonapi.PyThreadState_SetAsyncExc(
            ctypes.c_long(thread.ident), exc)
        if res == 0:
            raise ValueError("nonexistent thread id")
        elif res > 1:
            # """if it returns a number greater than one, you're in trouble,
            # and you should call it again with exc=NULL to revert the effect"""
            ctypes.pythonapi.PyThreadState_SetAsyncExc(thread.ident, None)
            raise SystemError("PyThreadState_SetAsyncExc failed")


if __name__ == '__main__':
    unittest.main()
