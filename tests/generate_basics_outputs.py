#!/usr/bin/env python3

import os
import sys
sys.path.append('.')
import contextlib
import io
from smedl import MonitorGenerator

testDir = 'tests/examples/basics/'
files = [f for f in os.listdir(testDir) if os.path.splitext(f)[1] == '.smedl']

for file in files:
    print(file)
    mgen = MonitorGenerator(console=True)
    with contextlib.redirect_stdout(io.StringIO()) as mgen_out:
        mgen.generate(os.path.join(testDir, os.path.splitext(file)[0]))
    mgen_out.seek(0)
    with open(os.path.join(testDir, os.path.splitext(file)[0] + '.out'), 'w') as ff:
        ff.write(mgen_out.read())