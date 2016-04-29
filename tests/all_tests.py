#!/usr/bin/env python
#-------------------------------------------------------------------------------
# tests/all_tests.py
#
# Run all SMEDL tests.
#
#-------------------------------------------------------------------------------
import subprocess, sys
from utils import is_in_rootdir

def run_test_script(path):
    cmd = [sys.executable, path]
    print("Running '%s'" % ' '.join(cmd))
    subprocess.check_call(cmd)

def main():
    if not is_in_rootdir():
        print('Error: Please run me from the root dir of smedl!')
        return 1
    run_test_script('tests/run_all_unittests.py')
    run_test_script('tests/run_examples_test.py')

if __name__ == '__main__':
    sys.exit(main())
