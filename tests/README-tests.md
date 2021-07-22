Tests
=====

This directory contains the automated tests for SMEDL. The project uses pytest
as its testing framework, which autodiscovers test scripts named `test_*.py`.
For more information on pytest, see the [pytest documentation][pytest-docs].

`tests` Directory Layout
------------------------

Inside this directory, you will find the following contents:

- `test_monitors.py`: Run tests on the generated monitors using the `rabbitmq`
  transport. The tests here should fully cover all features of the generated
  monitors. In the process, the `rabbitmq` adapter is also tested.

- `test_c_units.py`: Build and run C unit tests on the static C files

- `utils.py`: Helper functions and classes for the test modules

- `monitors/`: Contains all the monitors used for testing. Each monitor system
  gets its own subdirectory (named to match the `.a4smedl` file with the
  `.a4smedl` removed). In each subdirectory, there are:
  * `.smedl` and `.a4smedl` files
  * Any helper headers
  * Test cases, which are pairs of corresponding `.in` and `.out` files
  * `testinfo.json`, a file containing extra information used by some test
    scripts

- `bad_monitors/`: Like `monitors/`, but contains monitors where generation
  should fail. This is tested by the `test_invalid_monitor` test cases in
  `test_monitors.py`.

- `ctests/`: Contains C unit test code used by `test_c_units.py`. The top level
  contains unit tests for the common static files. Subdirectories contain unit
  tests for transport adapters.

- `ctests/unity/`: Contains the Unity library for the C unit tests. There is a
  submodule for the Unity repository and symbolic links to the important files.
  The submodule should be updated whenever there is a new version:

      cd ctests/unity/Unity
      git checkout v2.5.1
      cd ..
      git add unity
      git commit -m "Update Unity submodule to latest version"
      git push

  Then, other clones of the SMEDL repo must update:

      git pull
      git submodule update --init

- `docker/`: Contains the Dockerfile that can be used to build the GitLab CI/CD
  image

- `README-test.md`: This file

Note that there is no `__init__.py`. This directory is not a Python package. It
is simply a directory that contains all testing-related files. The various test
scripts are in fact executed as top-level modules (e.g. `test_monitors`, not
`tests.test_monitors`).

Example Monitors
----------------

The monitors in the `monitors/` directory can be useful examples of how to
write a SMEDL monitoring system. See the README with each monitor for a
description of what it does.

[pytest-docs]: https://docs.pytest.org/en/stable/
