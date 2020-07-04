Tests
=====

This directory contains the automated tests for SMEDL. The project uses pytest
as its testing framework, which autodiscovers test scripts named `test_*.py`.
For more information on pytest, see the [pytest documentation][pytest-docs].

`tests` Directory Layout
------------------------

Inside this directory, you will find the following contents:

- `test_monitors.py`: Run tests on the generated monitors using the `file`
  transport. The tests here should fully cover all features of the generated
  monitors. In the process, the `file` adapter is also tested.
- `test_rabbitmq.py`: Run tests on the generated monitors using the `rabbitmq`
  transport. The tests here cover the `rabbitmq` adapter.
- `monitors/`: Contains all the monitors used for testing. Each monitor system
  gets its own subdirectory (named to match the `.a4smedl` file with the
  `.a4smedl` removed).
- `bad_monitors/`: Like `monitors/`, but contains monitors where generation
  should fail. This is tested by the `test_invalid_monitor` test cases in
  `test_monitors.py`.
- `file/`: Contains test cases for `test_monitors.py`. One directory for each
  monitor to be tested (must match a directory in `monitors/`). Inside each one
  are the actual test cases: pairs of files `<testcase_name>.in` and
  `<testcase_name>.out`.
- TODO more directories
- `utils.py`: Helper functions and classes for the test modules
- `README-test.md`: This file

Note that there is no `__init__.py`. This directory is not a Python package. It
is simply a directory that contains all testing-related files. The various test
scripts are in fact executed as top-level modules (e.g. `test_monitors`, not
`tests.test_monitors`).

TODO
----

[pytest-docs]: https://docs.pytest.org/en/stable/
