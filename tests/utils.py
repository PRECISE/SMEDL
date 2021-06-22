"""
Classes and helper functions used by multiple test modules
"""

import pytest

import sys
import os
import os.path
import stat
import time
import subprocess
import tempfile
import json

import smedl

class TestingError(Exception):
    """Raised when there was an internal error in testing"""
    __test__ = False

def json_find_diff(actual, expected):
    """Return None if the two strings represent matching sequences of JSON
    objects (with multiple objects separated by whitespace).

    If they do not match, return the index (starting with 0) of the first
    object in "actual" that does not match "expected" or is invalid JSON.

    "expected" is assumed to be valid and an exception will be raised if it is
    not.
    """
    actual = actual.strip()
    expected = expected.strip()
    decoder = json.JSONDecoder()

    count = 0
    while len(expected) > 0:
        try:
            actual_json, actual_end = decoder.raw_decode(actual)
        except json.JSONDecodeError:
            return count
        expected_json, expected_end = decoder.raw_decode(expected)

        if actual_json != expected_json:
            return count

        actual = actual[actual_end:].lstrip()
        expected = expected[expected_end:].lstrip()
        count += 1

    if len(actual) > 0:
        return count

def parse_multiple_json(text):
    """Parse multiple JSON objects, separated by whitespace, from the input
    string. Return an iterator over the parsed objects. If the input string
    contains invalid JSON, a json.JSONDecodeError will be raised."""
    decoder = json.JSONDecoder()
    text.strip()
    count = 0
    while len(text) > 0:
        try:
            obj, end = decoder.raw_decode(text)
        except json.JSONDecodeError as e:
            raise json.JSONDecodeError("Object {}: ".format(count) + e.msg,
                    e.doc, e.pos) from e

        yield obj
        text = text[end:].lstrip()
        count += 1

def collect_test_cases():
    """Collect the list of monitors and test cases from the monitors/
    directory. Returns (monitors, test_cases) where monitors is a list of
    monitor names and test_cases is a list of (mon_name, test_case_name)."""
    # List of monitors
    test_monitors = os.listdir(os.path.join(sys.path[0], 'monitors'))
    # List of test case tuples
    test_cases = []
    for mon in test_monitors:
        files = os.listdir(os.path.join(sys.path[0], 'monitors', mon))
        for fname in files:
            root, ext = os.path.splitext(fname)
            if ext == '.in':
                test_cases.append((mon, root))
    return (test_monitors, test_cases)


class GeneratedMonitor:
    """Generates a monitor in a temporary directory on instantiation. Can run
    the monitor on demand."""

    def __init__(self, input_path, transport):
        """Generate the monitor.

        input_path - Path to the .a4smedl file to use
        """
        self.tmp_dir = tempfile.TemporaryDirectory()
        self.gen_dir = self.tmp_dir.name
        self.fname = os.path.splitext(os.path.basename(input_path))[0]
        self.generator = smedl.MonitorGenerator(out_dir=self.gen_dir,
                transport=transport)
        self.generator.generate(input_path)
        self.system = self.generator.system
        self.procs = None

    def build(self):
        """Build the monitor. Raise subprocess.CalledProcessError on failure.
        Return the path to the temp directory in case any config needs to be
        written."""
        subprocess.run('make', cwd=self.gen_dir, check=True)
        self.procs = []
        return self.gen_dir

    def run(self, capture_output, env=None, text=True):
        """Run the monitor. Finds every executable in the build directory and
        runs them all. Returns a list of the executables.

        capture_output - If False, stdout/stderr will not be captured and
          will write to the console like normal (but pytest may still capture
          them). If True, stdout/stderr will be captured and the output can be
          fetched with communicate().
        env - Optionally provide environment variables to the monitor
          processes.
        text - stdin and (if capture_output is true) stdout/stderr are opened
          in text mode, with newline translation ('\\n', '\\r', and '\\r\\n'
          are all translated to '\\n' for stdout/stderr and '\\n' in stdin is
          translated to the default line separator for the platform). This can
          be set to False if stdin/stdout/stderr need to be binary streams.
        """
        try:
            self.terminate()
        except TypeError:
            raise TestingError("Called GeneratedMonitor.run() before build()")

        stdout = None
        stderr = None
        self.needs_communicate = False
        if capture_output:
            stdout = subprocess.PIPE
            stderr = subprocess.PIPE
            self.needs_communicate = True

        self.procs = []
        for entry in os.scandir(self.gen_dir):
            mode = entry.stat().st_mode
            if stat.S_ISREG(mode) and (mode & stat.S_IXUSR):
                self.procs.append(subprocess.Popen(
                        os.path.join('.', entry.name),
                        stdin=subprocess.PIPE,
                        stdout=stdout,
                        stderr=stderr,
                        cwd=self.gen_dir,
                        env=env,
                        universal_newlines=text
                    ))

    def communicate(self, input_list=None, timeout=None):
        """Provide stdin to the monitor processes and read stdout/stderr (if
        capture_output was true). Blocks until all monitor processes exit. To
        then get their exit statuses, use wait().

        input_list - A list of input strings (if text was true, the default) or
          bytes (if text was false) to be used as stdin for the monitor
          processes. None may be used for some elements, in which case input
          will not be provided to that process. Or if None is provided in place
          of any list at all, input will not be provided to any process.
        timeout - Number of seconds to wait for each process before raising a
          TimeoutException

        Providing input is not recommended unless there is only one process:
        the first process must exit before the second receives input, and so
        on.

        Returns a list of 2-tuples (stdout, stderr), one per monitor process,
        in the same order they were returned from run(). If capture_output was
        false, stdout and stderr will be None. Otherwise, they will be strings
        (if text was true, the default) or bytes (if text was false).
        """
        result = []
        for i in range(len(self.procs)):
            if input_list is None:
                result.append(self.procs[i].communicate(timeout=timeout))
            else:
                result.append(self.procs[i].communicate(
                    input_list[i], timeout=timeout))
        self.needs_communicate = False
        return result

    def wait(self, timeout=None):
        """Wait for monitor processes to complete and get their exit statuses.
        Returns a list of exit statuses in the same order as the return from
        run()."""
        if self.needs_communicate:
            for proc in self.procs:
                proc.communicate(timeout)
            self.needs_communicate = False
        else:
            for proc in self.procs:
                proc.wait(timeout)
        return [proc.returncode for proc in self.procs]

    def terminate(self, timeout=5):
        """Terminate the monitor processes. Wait the timeout and then kill any
        remaining processes."""
        for proc in self.procs:
            if proc.returncode is None:
                proc.terminate()

        timeout_end = time.time() + timeout
        for proc in self.procs:
            timeout = timeout_end - time.time()
            try:
                proc.wait(timeout=(timeout if timeout > 0 else 0))
            except TimeoutError:
                pass

        for proc in self.procs:
            if proc.returncode is None:
                proc.kill()
