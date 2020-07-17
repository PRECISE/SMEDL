SMEDL Monitor Generator
=======================

A generator for runtime monitors

Homepage: [https://gitlab.precise.seas.upenn.edu/smedl/smedl/][repo]

Requirements
------------

These lists are primarily for reference only. The "Installation" section
below discusses all aspects of installation, including prerequisites.

**Python requirements:**

- [Python >=3.6][python]
- [TatSu >=4.4, \<5.0][tatsu]
- [Jinja2][jinja]
- [importlib\_resources >=1.1][importlib-resources] (only for Python 3.6.x)

For testing:

- [tox][tox]
- [pytest][pytest]
- [flake8][flake8]

**Monitor build requirements:**

- A C compiler (Any C99-compliant compiler should work)
- [rabbitmq-c][rabbitmq-c] (if using the RabbitMQ
  transport)
- [GNU make][make] recommended

Installation
------------

These instructions are designed for users on Unix-like systems (Linux, macOS).
Windows users might consider using Windows Subsystem for Linux or Cygwin, or
they may be able to adapt the instructions for native use.

Before you get started, make sure you have [Python][python] >=3.6 installed
with [pip][pip] available. The recommended installation method also requires
the `venv` module. Normally this will come with Python, but certain Linux
distributions package it as a separate install.

Download and extract a release or clone the repository:

    git clone https://gitlab.precise.seas.upenn.edu/smedl/smedl.git
    cd smedl

### Virtual Environments

Installing in a [virtual environment][venv] is recommended. This will keep all
dependencies for this project separate from the rest of the system, ensuring
there are no conflicts. Create the virtual environment like this:

    python3 -m venv .env

To use the virtual environment, you must activate it (note the dot at the
beginning of the line):

    . .env/bin/activate

Your prompt will start with `(.env)` to show you that it is active. In the
future, you will need to activate the virtual environment again each time you
open a new terminal (by using the same command). You will only be able to
install, upgrade, and use SMEDL while the virtual environment is active.

You must be in the `smedl` repository to activate the environment, but once it
is active, you can change to any directory without issue.

Once the environment is active, you may want to upgrade `pip` and `setuptools`
to the latest version (but this is not strictly necessary):

    pip install --upgrade pip setuptools

For more information on virtual environments, see the [virtual environment
tutorial][venv].

### Installation Proper

With the virtual environment active, SMEDL can be installed with pip:

    pip install .

This will automatically install all the prerequisites as well. That's it. *You
are now ready to run `mgen`.*

### Updating an Existing Installation

If you have pulled the latest commits in git or downloaded and unpacked the
latest release, you should be able to just install the new version over the
old version with the same command:

    pip install .

Nonetheless, if you would like to be extra sure, you can uninstall the previous
version before you install again:

    pip uninstall smedl
    pip install .

### Installation for Development

If you are installing to do development on SMEDL itself, you very likely want
to installing in editable mode (sometimes called "develop mode") by adding the
`-e` flag:

    pip install -e .

This will set it up so that changes you make to the code in the repository will
take effect immediately. Otherwise, you would have to reinstall SMEDL each time
you want to try out a change you made.

In addition, you probably want to install `tox`, which is used to run the test
suite:

    pip install tox

The tests require additional dependencies. Normally, there is no need to
install them manually, as `tox` handles that for you. But you may want to,
since you cannot run individual tests manually without them. The testing
dependencies can be installed like this:

    pip install -e .[test]

For more on testing, see the "Testing" section.

### Syntax Highlighting

If you use Vim, there are syntax highlighting files for SMEDL in the `vim/`
directory. Install them like this:

1. Copy both `smedl.vim` and `a4smedl.vim` to your `syntax/` directory:
   `~/.vim/syntax/` on Linux/macOS and `$HOME/vimfiles/syntax/` on Windows.
2. Create a `smedl.vim` file in `~/.vim/ftdetect/` (on Linux/macOS) or in
   `$HOME/vimfiles/ftdetect/` (on Windows) with just the following line:

       au BufRead,BufNewFile *.smedl set filetype=smedl

3. Create an `a4smedl.vim` file in a similar fashion (being sure to replace
   `smedl` with `a4smedl` in the line above).

Alternatively, for steps 2 and 3, you can simply add the lines to your regular
vimrc file.

Highlighting rules for Emacs and Visual Studio Code are on the roadmap, but
with fairly low priority.

### Uninstalling

If you installed using a virtual environment, you can uninstall simply by
deleting the virtual environment directory:

    rm -r .env/

Syntax highlighting files, just as they had to be installed manually, must be
removed manually.

Usage
-----

SMEDL works by reading monitor system specifications and translating them into
C source code. A monitor system consists of an architecture file (a.k.a. an
`.a4smdl` file) and one or more monitor specifications (a.k.a. `.smedl` files).
The monitor generator, `mgen`, is the program that translates these
specification files into C code.

This README assumes you already have `.smedl` and `.a4smedl` files ready for
use. For information on how to write those files, see the SMEDL Manual in
`doc/smedl.pdf`.

In its most basic form, here is the command to translate monitor specifications
into C code. Make sure your virtual environment is active before you run it.

    mgen [OPTIONS] [-d <dest_dir>] <input_file>

The `<input_file>` should be an `.a4smedl` file. This will generate all the C
code for that architecture file and all monitors it uses. The input file can
also be just a `.smedl` file, in which case only code for that monitor will be
generated (no local or global wrapper—see Part 2 of the manual, `doc/smedl.pdf`,
for more on what the wrappers do).

If the `-d` option is given, it will generate the code in the given directory.
Otherwise, it will generate code in the current directory.

There are some additional options for `mgen`. Some of these are discussed
shortly, but use `mgen --help` to see a full listing of options and what they
do.

### Transports

Events may be transmitted to and from monitors synchronously or asynchonously.
See the chapter on "A4SMEDL Specifications" in the manual (`doc/smedl.pdf`) for
more on that distinction. But for asynchronous transmission, SMEDL offers a few
transports to select from. This is done using the `-t <transport>` option.

The options are as follows:

- `rabbitmq`: Asynchronous events are transmitted as JSON-encoded RabbitMQ
  messages. This is a good choice when there is no compelling reason to pick
  another. A RabbitMQ server is required.
- `file`: Meant primarily for testing and debugging. Reads JSON-encoded events
  from a file (or stdin) and writes exported events to stdout. Events between
  monitors are not actually asynchronous.

Additional transport adapters are in development.

If no transport option is chosen, the generated monitors will only support
synchronous communication, i.e. event transmission by linking against them and
using their C API directly. *Note that synchronous sets cannot transmit events
to each other directly without an asynchronous transport.*

For more information on the specifics of each transport, see the chapter on
"Transport Adapters" in the SMEDL manual (`doc/smedl.pdf`).

### Makefile Generation and Compiling

When a transport option is chosen (`-t`), `mgen` has the ability to
automatically generate a makefile. If there is not already a file named
`Makefile` in the destination directory, it will do so.

If no transport option is chosen, or there does already exist a file named
`Makefile`, a makefile will not automatically be generated.

You can force makefile generation, even when it would overwrite an existing
`Makefile`, with the `-m` option (but even so, a `-t` option is still
required). On the other hand, if you want to inhibit makefile generation, use
the `--no-makefile` option.

When `mgen` generates a makefile for you, the monitors can be built simply by
running `make`. If you like, there are some options to tweak the build at the
top of the makefile.

For cases where `mgen` does not generate a makefile, or you are opting not to
use it, the following tips may be helpful:

- Generally speaking, each synchronous set is built into its own executable.
  (The exception is when using the file transport, where all synchronous sets
  are linked into a single executable.)
- Any files with the monitor names or synchronous set name, along with all the
  static files (e.g. `smedl_types.c`, `event_queue.c`, etc.), are compiled
  together as part of one synchronous set.
- The generated code conforms to C99. You may want to use the `-std=c99` option
  for your compiler.
- If you want to see extra diagnostic messages, define the `DEBUG` flag with an
  integer 1-4. Using 0 is the same as not defining it at all. These are the
  debug levels:
  * `-DDEBUG=0` Debug messages off
  * `-DDEBUG=1` Errors only (serious conditions that cannot be recovered from)
  * `-DDEBUG=2` Errors and warnings (Non-serious abnormal conditions)
  * `-DDEBUG=3` Errors, warnings and notices (significant but normal)
  * `-DDEBUG=4` Full debug output

For information about the API for generated code and how to integrate SMEDL
monitors into your existing systems, see Part 2 of the SMEDL manual
(`doc/smedl.pdf`).

Examples
--------

See the `tests/monitors/` directory for several examples of working monitor
systems. The `tests/README-tests.md` file has short descriptions of each
monitor.

Testing
-------

SMEDL uses [`tox`][tox] to run the test suite. You must install it manually:

    pip install tox

To run the full test suite, change directories to the SMEDL repository and run:

    tox

The test suite includes the following:

- `setup.py check`: Does basic verifications on `setup.py`
- [flake8][flake8]: Style checks and basic static code analysis for the Python
  code
- [pytest][pytest]: Run the test scripts in the `tests/` directory. See
  `tests/README-tests.md` for more information.

By default, `tox` will run the test suite using all Python versions that are
still being maintained (currently 3.6, 3.7, and 3.8) to ensure there are no
issues with any of them. If you do not have all of them installed, you will get
errors. In that case, you can tell `tox` to run only your default version of
Python 3:

    tox -e py3

The full test suite with all Python versions automatically runs on GitLab in
certain circumstances:

- Commits to the `master` branch or any `dev*` branch
- Merge requests
- Any tagged commits
- Any commits whose commit message contains `run ci`
- *Exception:* The test suite will never run if the commit message contains
  `skip ci`

Sometimes, you may want to run specific components of the test suite or even
specific tests manually. Normally, `tox` handles installing all the test
dependencies in a separate, dedicated virtual environment. If you want to run
tests outside of `tox`, you will need to install these dependencies in your
regular virtual environment:

    pip install -e .[test]

Now, you can run `setup.py check`, `flake8 smedl/`, `pytest`, or
`pytest -k <test_name>`  manually. These all should be run in the top-level
directory of the repository.

Further Reading
---------------

The full SMEDL manual can be found in `doc/smedl.pdf`. It describes the SMEDL
language and the API for generated monitors in detail. There are some other
documents in the same directory that might be helpful, as well.

License and Contact
-------------------

Copyright © 2020 The Trustees of the University of Pennsylvania

Licensed under a TODO license. For full details, see `LICENSE.txt`.

Contact: Dominick Pastore [\<dpastore@seas.upenn.edu>](mailto:dpastore@seas.upenn.edu)


[repo]: https://gitlab.precise.seas.upenn.edu/smedl/smedl/
[python]: https://www.python.org/
[pip]: https://pip.pypa.io/en/stable/
[tatsu]: https://github.com/neogeny/TatSu
[jinja]: https://palletsprojects.com/p/jinja/
[importlib-resources]: https://pypi.org/project/importlib-resources/
[tox]: https://tox.readthedocs.io/en/latest/
[pytest]: https://docs.pytest.org/en/latest/
[flake8]: https://flake8.pycqa.org/en/latest/
[rabbitmq-c]: http://alanxz.github.io/rabbitmq-c/
[make]: https://www.gnu.org/software/make/
[venv]: https://docs.python.org/3/tutorial/venv.html
