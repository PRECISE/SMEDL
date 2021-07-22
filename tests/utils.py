"""
Classes and helper functions used by multiple test modules
"""

import pytest

import asyncio
import os
import os.path
import stat
import subprocess
import sys
import tempfile

import smedl


class TestingError(Exception):
    """Raised when there was an internal error in testing"""
    __test__ = False


def collect_test_cases():
    """Collect the list of monitors and test cases from the monitors/
    directory. Returns (monitors, test_cases) where monitors is a list of
    monitor names and test_cases is a list of
    (mon_name, test_case_name, exec_list) where exec_list is a list of
    monitor executables with input files for this test
    """
    # List of monitors
    test_monitors = os.listdir(os.path.join(sys.path[0], 'monitors'))
    # List of test case tuples
    all_test_cases = []
    for mon in test_monitors:
        # Input files are named like <test_case>.<executable_name>.in
        test_cases = dict()
        files = os.listdir(os.path.join(sys.path[0], 'monitors', mon))
        for fname in files:
            root, ext = os.path.splitext(fname)
            if ext == '.in':
                test_name, _, exec_name = root.partition('.')
                try:
                    test_cases[test_name].append(exec_name)
                except KeyError:
                    test_cases[test_name] = [exec_name]
        for test_name, file_list in test_cases.items():
            all_test_cases.append((mon, test_name, file_list))

    return (test_monitors, all_test_cases)


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
        self.built = False

    def build(self):
        """Build the monitor. Raise subprocess.CalledProcessError on failure.
        Return the path to the temp directory in case any config needs to be
        written."""
        subprocess.run('make', cwd=self.gen_dir, check=True)
        self.built = True
        return self.gen_dir

    def run(self, stdin=dict(), timeout=None, env=None, text=True):
        """Run the monitor. Finds every executable in the build directory and
        runs them all. Stdin for each process can optionally be provided, and
        stdout/stderr will be collected. The return value is a tuple of dicts
        (executable_name => stdout, executable_name => stderr).

        Parameters:
        stdin - A dict of executable_name => string/bytes. Any executables
          omitted or set to None will not be fed anything for stdin.
        timeout - Number of seconds to allow monitors to run before terminating
          them.
        env - Optionally provide environment variables to the monitor processes.
        text - By default, stdin/out/err for each process are opened in text
          mode. That means input/output will be as strings with universal
          newline translation. If set to False, stdin/out/err will be opened in
          binary mode and input/output will be as bytes without newline
          translation.
        """
        if self.built == False:
            raise TestingError("Called GeneratedMonitor.run() before build()")

        # Collect executable names and stdins
        procs = []
        stdin_full = dict()
        for entry in os.scandir(self.gen_dir):
            mode = entry.stat().st_mode
            if stat.S_ISREG(mode) and (mode & stat.S_IXUSR):
                procs.append(entry.name)
                this_stdin = stdin.pop(entry.name, None)
                if text and this_stdin is not None:
                    this_stdin = this_stdin.encode()
                stdin_full[entry.name] = this_stdin
        if len(stdin) > 0:
            raise ValueError("stdin dict contains entries for nonexistent "
                             "executables: " + ", ".join(stdin.keys()))

        # Call self._run_monitors coroutine
        try:
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            ret_val = loop.run_until_complete(
                self._run_monitors(procs, stdin_full, timeout, env))
        finally:
            loop.close()

        # Create and return results dicts
        if text:
            return ({proc: out.decode() for proc, out, _ in ret_val},
                    {proc: err.decode() for proc, _, err in ret_val})
        else:
            return ({proc: out for proc, out, _ in ret_val},
                    {proc: err for proc, _, err in ret_val})

    async def _run_single_monitor(self, proc_name, stdin, timeout, env):
        """Run a single executable asynchronously with a timeout. Return a
        tuple with the process name and its output."""
        # Create subprocess and send stdin
        proc = await asyncio.create_subprocess_exec(
            os.path.join('.', proc_name),
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            cwd=self.gen_dir,
            env=env)
        comm_future = asyncio.ensure_future(proc.communicate(stdin))

        # Wait the timeout and kill if necessary
        done, pending = await asyncio.wait((comm_future,), timeout=timeout)
        if len(pending) > 0 and proc.returncode is None:
            # Subprocess didn't finish communicating before the timeout.
            try:
                proc.kill()
            except OSError:
                pass

        # Get the output
        out, err = await comm_future
        return proc_name, out, err

    async def _run_monitors(self, procs, stdin, timeout, env):
        """Actually run the listed executables asynchronously"""
        subprocesses = []
        for proc in procs:
            subprocesses.append(
                self._run_single_monitor(proc, stdin[proc], timeout, env))

        ret_val = await asyncio.gather(*subprocesses)
        return ret_val
