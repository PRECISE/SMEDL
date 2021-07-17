SMEDL Monitor Generator
=======================

A runtime verification framework to specify monitors using an EFSM-style
formalism, to generate C executable monitor code from specifications, and to
deploy the monitors in centralized or distributed settings.

Full manual: [http://precise.github.io/SMEDL][man]
Git repository: [https://github.com/PRECISE/SMEDL][repo]

Requirements
------------

These lists are primarily for reference only. The "Installation" section
below discusses all aspects of installation, including prerequisites.

**Python requirements:**

- [Python][python] >=3.6
- [TatSu][tatsu] >=4.4 (and \<5.0 for Python \<3.7.x)
- [Jinja2][jinja] >=3.0
- [importlib\_resources][importlib-resources] >=1.1 (only for Python 3.6.x)
- Required only for testing:
  * [tox][tox]
  * [pytest][pytest]
  * [flake8][flake8]
  * A [RabbitMQ server][rabbitmq-install] (Not Python software, but required
    for RabbitMQ tests)

**Monitor build requirements:**

- A C compiler (Any C99-compliant compiler should work)
- [rabbitmq-c][rabbitmq-c] (if using the RabbitMQ transport)
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

    git clone https://github.com/PRECISE/SMEDL.git
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

In addition, you probably want to install `tox` and a RabbitMQ server. `tox` is
used to run the test suite, and a RabbitMQ server is required for the RabbitMQ
tests. Install `tox` with this command:

    pip install tox

On Ubuntu, a RabbitMQ server can be installed with
`sudo apt install rabbitmq-server`. Other platforms may have versions packaged
in their respective repositories, or you can install the latest version from
the [RabbitMQ website]. Alternatively, if you have access to an existing
RabbitMQ server, you can configure the tests to use that. See the "Testing"
section for more details.

The tests require additional Python dependencies. Normally, there is no need to
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
`.a4smedl` file) and one or more monitor specifications (a.k.a. `.smedl`
files). The monitor generator, `mgen`, is the program that translates these
specification files into C code.

This README assumes you already have `.smedl` and `.a4smedl` files ready for
use. For information on how to write those files, see the [SMEDL Manual][man].

In its most basic form, here is the command to translate monitor specifications
into C code. Make sure your virtual environment is active before you run it.

    mgen [OPTIONS] [-d <dest_dir>] <input_file>

The `<input_file>` should be an `.a4smedl` file. This will generate all the C
code for that architecture file and all monitors it uses. The input file can
also be just a `.smedl` file, in which case only code for that monitor will be
generated (no local or global wrapper—see the [SMEDL manual][man] for more on
what the wrappers do).

Unless you have no asynchronous events (that is, you have one synchronous set
and it contains all the PEDL events as well), you probably want to use the `-t`
option to generate a transport as well. See the following section for more on
that.

If the `-d` option is given, it will generate the code in the given directory.
Otherwise, it will generate code in the current directory.

There are some additional options for `mgen`. Use `mgen --help` to see a full
listing of options and what they do.

### Transports

Events may be transmitted to and from monitors synchronously or asynchonously.
See the page on "architecture Specifications" in the [SMEDL manual][man] for
more on that distinction. But for asynchronous transmission, SMEDL offers a few
transports to select from. This is done using the `-t <transport>` option.

The options are as follows:

- `rabbitmq`: Asynchronous events are transmitted as JSON-encoded RabbitMQ
  messages. This is a good choice when there is no compelling reason to pick
  another. You will need [rabbitmq-c][rabbitmq-c] installed to build monitors
  with this transport and a RabbitMQ server to run them.
- `ros`: Generates a ROS node for each synchronous set. Asynchronous events are
  transmitted via ROS topics. Message files are automatically generated for
  each event, or you can specifiy which existing topics and message types to
  use (for tying into an existing system).

For a pure asynchronous monitoring system (that is, all monitors and the `pedl`
keyword are in a single synchronous set), chances are the `rabbitmq` transport
is the correct choice. Mgen is smart enough to recognize that the actual
RabbitMQ code is unnecessary in this case, but you will still get a complete
monitoring system with a Makefile.

For more information on the specifics of each transport, see the [SMEDL
manual][man].

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
running `make`. (This, of course, assumes you have a C compiler and GNU make
installed.) If you like, there are some options to tweak the build at the top
of the makefile.

For cases where `mgen` does not generate a makefile, or you are opting not to
use it, the following tips may be helpful:

- Generally speaking, each synchronous set is built into its own executable.
- Any files with the synchronous set name, files with names of monitors within
  that synchronous set, and all the static files (e.g. `smedl_types.c`,
  `monitor_map.c`, etc.), are compiled together as part of one synchronous set.
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
monitors into your existing systems, see the [SMEDL manual][man].

Examples
--------

See the `tests/monitors/` directory for several examples of working monitor
systems. The README in each monitor directory has a brief description of the
monitor.  Note that there are extra files present in the example monitor
directories that are only used for testing purposes. Only the `.smedl` and
`.a4smedl` files are the actual monitors.

Testing
-------

SMEDL uses [`tox`][tox] to run the test suite. See the "Installation for
Development" section for information on installing that and a RabbitMQ server
needed by the RabbitMQ tests.

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

### Running Tests Manually

Sometimes, you may want to run specific components of the test suite or even
specific tests manually. Normally, `tox` handles installing all the test
dependencies in a separate, dedicated virtual environment. If you want to run
tests outside of `tox`, you will need to install these dependencies in your
regular virtual environment:

    pip install -e .[test]

Now, you can run `setup.py check`, `flake8 smedl/`, `pytest`, or
`pytest -k <test_name>`  manually. These all should be run in the top-level
directory of the repository.

### Using an External RabbitMQ Server

If you have access to an existing RabbitMQ server, you can configure the test
framework to use that instead of a locally installed server. This is also
useful if you need to change any other RabbitMQ options, such as the port,
username/password, or vhost.

There are two options for this:

1. Provide extra arguments to `tox`:

       tox -- --rabbitmq-server rabbitmq.example.com

2. Store the extra arguments in an environment variable named `PYTEST_ARGS`:

       export PYTEST_ARGS="--rabbitmq-server rabbitmq.example.com"
       tox

Here is the full list of options you can set:

- `--rabbitmq-server`: The hostname or IP address for the RabbitMQ server
- `--rabbitmq-port`: The port to use for the RabbitMQ server
- `--rabbitmq-user`: The username for the RabbitMQ server
- `--rabbitmq-pass`: The password for the RabbitMQ server
- `--rabbitmq-vhost`: The vhost to use with the RabbitMQ server
- `--rabbitmq-exchange`: The exchange to use with the RabbitMQ server

Full Manual
-----------

The full SMEDL manual can be found online at
[http://precise.github.io/SMEDL][man] or a PDF form can be generated by
installing [Sphinx][sphinx-install] and running `make latexpdf` in the `docs/`
directory.

License and Contact
-------------------

Copyright © 2021 The Trustees of the University of Pennsylvania

Licensed under an MIT license. For full details, see `LICENSE.txt`.

Contact: Teng Zhang [\<tengz@seas.upenn.edu>](mailto:tengz@seas.upenn.edu),
Dominick Pastore [\<dpastore@seas.upenn.edu>](mailto:dpastore@seas.upenn.edu)


[repo]: https://github.com/PRECISE/SMEDL
[python]: https://www.python.org/
[pip]: https://pip.pypa.io/en/stable/
[tatsu]: https://github.com/neogeny/TatSu
[jinja]: https://palletsprojects.com/p/jinja/
[importlib-resources]: https://pypi.org/project/importlib-resources/
[tox]: https://tox.readthedocs.io/en/latest/
[pytest]: https://docs.pytest.org/en/latest/
[flake8]: https://flake8.pycqa.org/en/latest/
[pika]: https://pika.readthedocs.io/en/stable/
[rabbitmq-install]: https://www.rabbitmq.com/download.html
[rabbitmq-c]: http://alanxz.github.io/rabbitmq-c/
[make]: https://www.gnu.org/software/make/
[venv]: https://docs.python.org/3/tutorial/venv.html
[man]: http://precise.github.io/SMEDL
[sphinx-install]: https://www.sphinx-doc.org/en/master/usage/installation.html
