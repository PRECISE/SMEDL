import unittest
import subprocess

class TestSpv(unittest.TestCase):

    def test_mgen(self):
        mgenCall = subprocess.run(["python3", "-m", "smedl.mgen", "-c", "tests/examples/spv-rabbitmq/spv"], stdout=subprocess.PIPE)

    def test_compile(self):
        mgenCall = subprocess.run(["python3", "-m", "smedl.mgen", "-c", "tests/examples/spv-rabbitmq/spv"], stdout=subprocess.PIPE)

    def test_run(self):
        mgenCall = subprocess.run(["python3", "-m", "smedl.mgen", "-c", "tests/examples/spv-rabbitmq/spv"], stdout=subprocess.PIPE)

if __name__ == '__main__':
    unittest.main()
