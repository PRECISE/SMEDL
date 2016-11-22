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

class TestString(unittest.TestCase):

    def setUp(self):
        self.origPath = os.getcwd()

    def tearDown(self):
        os.chdir(self.origPath)

    def test_string_mgen(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/string_test/smedl/string","--arch=tests/examples/string_test/smedl/stringArch"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_string_mgen1(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/string_test/smedl/stringVariableUpdate","--arch=tests/examples/string_test/smedl/stringArch"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_string_mgen2(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/string_test/smedl/stringLiteral","--arch=tests/examples/string_test/smedl/stringArch"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_string_mgen3(self):
        call = subprocess.run(["python3", "-m", "smedl.mgen", "--dir", "../gen", "tests/examples/string_test/smedl/stringLiteral2","--arch=tests/examples/string_test/smedl/stringArch"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def test_string_compile(self):
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'string_test')))
        os.makedirs('bin', exist_ok=True)
        call = subprocess.run("make all", shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(0, call.returncode)

    def test_string_run(self):
        global test_step
        os.chdir(str(pathlib.PurePath('.', 'tests', 'examples', 'string_test')))
        with open('string_mon.cfg', 'r') as cfgfile:
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
        channel1.queue_bind(exchange=cfg['rabbitmq']['exchange'], queue=queue_name1,routing_key='stringtest_pong.#')

        channel2 = connection.channel()
        channel2.exchange_declare(exchange=cfg['rabbitmq']['exchange'], exchange_type='topic', durable=True)
        result2 = channel2.queue_declare(exclusive=True)
        queue_name2 = result2.method.queue
        channel2.queue_bind(exchange=cfg['rabbitmq']['exchange'], queue=queue_name1,routing_key='stringLiteralTest_pong.#')


        def callback(ch, method, properties, body):
            global test_step
            body = str(body, 'utf-8')
            print(body)
            if test_step < 2:
                test_step += 1
            if test_step == 2:
                test_step += 1
                channel.basic_publish(exchange=cfg['rabbitmq']['exchange'],
                routing_key='ch1.foo', body="{\"name\":\"0\", \"fmt_version\":\"1.0.0\", \"params\":{\"v1\": \"0\", \"v2\":2}}")
                channel.basic_publish(exchange=cfg['rabbitmq']['exchange'],
                routing_key='ch2.foo', body="{\"name\":\"0\", \"fmt_version\":\"1.0.0\" }")
            #elif test_step == 2 and "\"v1\":	\"0\"" in body and "\"v2\":	3" in body and "\"v3\":	1500" in body:
            elif test_step == 3 and "pong" in body or "\"0\"" in body:
                test_step += 1
            elif test_step == 4 and "pong" in body or "\"0\"" in body:
                test_step += 1

        channel.basic_consume(callback, queue=queue_name, no_ack=True)
        recieve_thread = threading.Thread(target=channel.start_consuming)
        recieve_thread.start()

        channel1.basic_consume(callback, queue=queue_name1, no_ack=True)
        recieve_thread1 = threading.Thread(target=channel1.start_consuming)
        recieve_thread1.start()

        channel2.basic_consume(callback, queue=queue_name1, no_ack=True)
        recieve_thread2 = threading.Thread(target=channel2.start_consuming)
        recieve_thread2.start()

        if connection is None:
            self.fail()
        call = subprocess.Popen("./bin/string_test", shell=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        call2 = subprocess.Popen("./bin/stringLiteral_test", shell=True,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        time.sleep(1)
        self.assertEqual(5, test_step)
        test_step = 0
        call.terminate()
        call2.terminate()
        call3 = subprocess.Popen("./bin/string_test2", shell=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        call4 = subprocess.Popen("./bin/stringLiteral_test2", shell=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        time.sleep(1)
        call3.terminate()
        call4.terminate()
        self.terminate_thread(recieve_thread)
        self.terminate_thread(recieve_thread1)
        self.terminate_thread(recieve_thread2)
        self.assertEqual(5, test_step)


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
