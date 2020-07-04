"""
Classes and helper functions used by multiple test modules
"""

import pytest

import os
import os.path
import stat
import time
import subprocess
import tempfile

import smedl

class TestingError(Exception):
    """Raised when there was an internal error in testing"""

def _is_whitespace(c):
    return c in (' ', '\t', '\n', '\r')

def _is_number(c):
    return c in ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+',
            '-', '.', 'e', 'E')

def _is_number_start(c):
    return c in ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+',
            '-', '.', 'e', 'E')

class _MantissaExp:
    """A number in a floating point format converted from JSON string"""
    def __init__(self, num_str):
        self.positive = True
        self.mantissa = 0
        self.exponent = -1

        i = 0
        end = len(num_str)
        if end == 0:
            raise ValueError('Empty string')

        # Check if negative
        if num_str[i] == '-':
            self.positive = False
            i += 1

        if i == end:
            raise ValueError('No integer part')

        # Leading zero only allowed if integer part is zero
        if num_str[i] != '0':
            self.exponent = 0
            self.mantissa = ord(num_str[i]) - ord('0')
            if not 0 < self.mantissa <= 9:
                raise ValueError('Invalid integer part')

            while True:
                i += 1
                if i == end:
                    return
                digit = ord(num_str[i]) - ord('0')
                if not 0 <= digit <= 9:
                    break
                self.mantissa = self.mantissa * 10 + digit
                self.exponent += 1
        else:
            i += 1

        # Check if fraction part
        if i + 1 < end and num_str[i] == '.':
            i += 1
            digit = ord(num_str[i]) - ord('0')
            if not 0 <= digit <= 9:
                raise ValueError('Invalid fraction part')
            self.mantissa = self.mantissa * 10 + digit

            while True:
                i += 1
                if i == end:
                    return
                digit = ord(num_str[i]) - ord('0')
                if not 0 <= digit <= 9:
                    break
                self.mantissa = self.mantissa * 10 + digit

        # Check if exponent part
        if i + 1 < end and num_str[i] in ('e', 'E'):
            i += 1
            if num_str[i] == '+':
                exp_positive = True
                i += 1
            elif num_str[i] == '-':
                exp_positive = False
                i += 1
            else:
                exp_positive = True

            if i == end:
                raise ValueError('Invalid exponent part')

            exp = 0
            while True:
                digit = ord(num_str[i]) - ord('0')
                if not 0 <= digit <= 9:
                    raise ValueError('Invalid exponent part')
                exp = exp * 10 + digit
                i += 1
                if i == end:
                    break

            if exp_positive:
                self.exponent += exp
            else:
                self.exponent -= exp

        if i < end:
            raise ValueError('Invalid number')

    def __eq__(self, other):
        if isinstance(other, _MantissaExp):
            if self.mantissa == 0 == other.mantissa:
                return True
            if self.positive != other.positive:
                return False
            if self.exponent < other.exponent:
                diff = other.exponent - self.exponent
                return self.mantissa * 10 ** diff == other.mantissa
            elif self.exponent > other.exponent:
                diff = self.exponent - other.exponent
                return other.mantissa * 10 ** diff == self.mantissa
            return other.mantissa == self.mantissa
        return False

def _number_matches(actual, expected):
    """Compare two JSON numbers for equality"""
    try:
        acutal = _MantissaExp(actual)
        expected = _MantissaExp(expected)
        return actual == expected
    except ValueError:
        return False

def json_matches(actual, expected):
    """Return True if the two strings represent matching sequences of JSON
    objects, False otherwise. Multiple JSON objects are to be separated by
    whitespace. Object members must appear in the same order.

    expected - The object(s) to compare against. Assumed to be valid JSON.
    actual - The object(s) that must match. If not valid JSON, False will be
      returned.

    Limitations: Numbers must match precisely, no rounding error. Escape
    sequences in strings are not expanded and must match verbatim. Some invalid
    number formats may not be rejected.
    """

    i, j = 0, 0
    end_i = len(actual)
    end_j = len(expected)

    in_string = False
    backslash = False
    num_start_i = None  # Start of current number in actual
    num_start_j = None  # Start of current number in expected
    keyword = 0  # Number of chars left in current keyword (true, false, null)

    while i < end_i and j < end_j:
        if in_string:
            # Strings must match perfectly. 
            if backslash:
                backslash = False
            else:
                if expected[j] == '\\':
                    backslash = True
                elif expected[j] == '"':
                    in_string = False
            if actual[i] != expected[j]:
                return False

        elif num_start_j is not None:
            # In a number.
            if not _is_number(expected[j]):
                if not _number_matches(actual[num_start_i:i],
                        expected[num_start_j:j]):
                    return False
                num_start_i = None
                num_start_j = None
                # Go back to the top of the while so the last elif is entered
                continue

        elif keyword > 0:
            # In a keyword
            if actual[i] != expected[j]:
                return False
            keyword -= 1

        elif _is_whitespace(expected[j]):
            # Skip whitespace in expected and actual
            while _is_whitespace(expected[j]) and j < end_j:
                j += 1
            while _is_whitespace(actual[i]) and i < end_i:
                i += 1
        elif _is_whitespace(actual[i]):
            # Skip whitespace in actual (expected had none_
            while _is_whitespace(actual[i]) and i < end_i:
                i += 1

        else:
            # Not currently in a number or a string.
            if expected[j] == '"':
                in_string = True
            elif expected[j] == 't' or expected[j] == 'n':
                keyword = 3
            elif expected[j] == 'f':
                keyword = 4
            elif _is_number(expected[j]):
                num_start_i = i
                num_start_j = j
                # Go back to the top of the while so the number elif is entered
                continue
            if actual[i] != expected[j]:
                return False

        i += 1
        j += 1

    # May have been in a number at the end of the string. Make sure it matches.
    if num_start_j is not None:
        if not _number_matches(actual[num_start_i:i], expected[num_start_j:j]):
            return False

    return i == end1 and j == end2

class GeneratedMonitor:
    """Generates a monitor in a temporary directory on instantiation. Can run
    the monitor on demand."""

    def __init__(input_path, transport):
        """Generate the monitor.

        input_path - Path to the .a4smedl file to use
        """
        self.gen_dir = tempfile.TemporaryDirectory()
        self.fname = os.path.splitext(os.path.basename(input_path))[0]
        self.generator = smedl.MonitorGenerator(out_dir=self.gen_dir.name,
                transport=transport)
        self.generator.generate(input_path)
        self.system = self.generator.system
        self.procs = None

    def build():
        """Build the monitor. Raise subprocess.CalledProcessError on failure.
        Return the path to the temp directory in case any config needs to be
        written."""
        subprocess.run('make', cwd=self.gen_dir, check=True)
        self.procs = []
        return self.gen_dir

    def run(capture_output, env=None, text=True):
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
                        entry.name,
                        stdin=subprocess.PIPE,
                        stdout=stdout,
                        stderr=stderr,
                        cwd=self.gen_dir,
                        env=env,
                        universal_newlines=text
                    ))

    def communicate(input_list=None, timeout=None):
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
        return result

    def wait(timeout=None):
        """Wait for monitor processes to complete and get their exit statuses.
        Returns a list of exit statuses in the same order as the return from
        run()."""
        if self.needs_communicate:
            for proc in self.procs:
                proc.communicate(timeout)
        else:
            for proc in self.procs:
                proc.wait(timeout)
        return [proc.returncode for proc in self.procs]

    def terminate():
        """Terminate the monitor processes. Wait two seconds and then kill any
        remaining processes."""
        for proc in self.procs:
            if proc.returncode is None:
                proc.terminate()
        time.sleep(2)
        for proc in self.procs:
            if proc.returncode is None:
                proc.kill()
