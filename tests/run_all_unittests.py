#!/usr/bin/env python
#-------------------------------------------------------------------------------
# tests/run_all_unittests.py
#
# Run all unit tests (alternative to running 'python -m unittest discover ...')
#
#-------------------------------------------------------------------------------
import os, sys

try:
    import unittest2 as unittest
except ImportError:
    import unittest


def main():
    if not os.path.isdir('tests'):
        print('!! Please execute from the root directory of smedl')
        return 1
    else:
        tests = unittest.TestLoader().discover('tests', 'test*.py', 'tests')
        result = unittest.TextTestRunner().run(tests)
        if result.wasSuccessful():
            return 0
        else:
            return 1

if __name__ == '__main__':
    sys.exit(main())
