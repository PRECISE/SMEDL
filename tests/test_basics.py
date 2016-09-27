from smedl import MonitorGenerator
import os
import unittest
import contextlib
import sys
import io

class TestBasics(unittest.TestCase):

    def setUp(self):
        self.testDir = 'tests/examples/basics/'
        self.files = [f for f in os.listdir(self.testDir) if os.path.splitext(f)[1] == '.smedl']

    def test_basics(self):
        for file in self.files:
            self.mgen = MonitorGenerator(console=True)
            with open(os.path.join(self.testDir, os.path.splitext(file)[0] + '.out'), 'r') as outFile:
                out = outFile.read()
            with contextlib.redirect_stdout(io.StringIO()) as mgen_out:
                self.mgen.generate(os.path.join(self.testDir, os.path.splitext(file)[0]))
            mgen_out.seek(0)
            self.assertEqual(mgen_out.read(), out, msg=file)

if __name__ == '__main__':
    unittest.main()