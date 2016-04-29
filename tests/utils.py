#-------------------------------------------------------------------------------
# test/utils.py
#
# Some common utils for tests
#
# Eli Bendersky (eliben@gmail.com)
# This code is in the public domain
#-------------------------------------------------------------------------------
import os, sys, subprocess, tempfile

# This module should not import elftools before setup_syspath() is called!
# See the Hacking Guide in the documentation for more details.

def setup_syspath():
    """ Setup sys.path so that tests pick up local smedl code before the
        installed one when run from development directory.
    """
    if sys.path[0] != '.':
        sys.path.insert(0, '.')


def is_in_rootdir():
    """ Check whether the current dir is the root dir of smedl project
    """
    return os.path.isdir('smedl') and os.path.isdir('tests')


def dump_output_to_temp_files(testlog, *args):
    """ Dumps the output strings given in 'args' to temp files: one for each
        arg.
    """
    for i, s in enumerate(args):
        fd, path = tempfile.mkstemp(
                prefix='out' + str(i + 1) + '_',
                suffix='.stdout')
        file = os.fdopen(fd, 'w')
        file.write(s)
        file.close()
        testlog.info('@@ Output #%s dumped to file: %s' % (i + 1, path))

