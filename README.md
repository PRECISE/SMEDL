# SMEDL/PEDL Monitor Generator
### Version 1.0

## Requirements
--------------
1. [Python 3](https://docs.python.org/3/)
2. [pip](https://pip.pypa.io/en/stable/)
    - [Grako 3.14](https://pythonhosted.org/grako/)
    - [Jinja2 2.8](http://jinja.pocoo.org/)

## Getting started
---------------
A [Python virtual environment](https://docs.python.org/3/library/venv.html)
including [Python 3](https://docs.python.org/3/) and all required Python
packages has been defined to simplify the process of getting started with the
tool.

If you want to use a virtual environment (recommended), set it up by running
the following command from the project's root directory:
```sh
pyvenv .env && source .env/bin/activate
```

To install all of the required dependencies from PyPi and install the monitor
generator `mgen` as an executable on your path, run the following command in
the root of the repository:
```sh
pip install .
```

To update the installation of `mgen` without updating its dependencies, run
```sh
pip uninstall smedl
pip install .
```


## Generating the monitor
----------------------
The 'mgen' script is the primary interface for generating software monitors
from SMEDL and PEDL definitions. This script can be run with the following
command (from the project root directory):

`python -m smedl.mgen PEDL_SMEDL_FILENAME`

This script will generate C source code representing a runtime monitor as
specified by the PEDL and SMEDL definitions, along with necessary monitor
management infrastructure.

To allow the script to properly locate the PEDL and SMEDL files, the script's
single parameter should be the name used by the PEDL and SMEDL files, and that
name should be identical for both files except for their file extensions, .pedl
and .smedl.

Note: There are two debug flags that can be specified at the command-line.
These are the '-s' flag for displaying the contents of internal data structures
used by the monitor during its generation steps and the '-d' flag for
outputting various debug statements written in the monitor generator code.

Other useful flags:
  ```sh
  --helper <HEADER FILE> : Include the specified header file for providing helper functions
  --console : Forces output to only show in the console; no file output will be generated
  --noimplicit : Disables implicit error handling in the generated monitor
  --arch <ARCH FILE> : The name of architechture file to parse (Described further below)
  ```


## Instrumenting the target
------------------------
At the moment, instrumentation of the target program must be performed
manually. The generated event handling functions, or 'probes', can be found in
the {object}\_mon.h file. The probe naming convention uses the monitor object
name and the event name, separated by an underscore. Probes can be added
anywhere in the target program (assuming the PEDL definitions are followed) and
will be compiled with the target if the expected parameters are provided and
the {object}\_mon.h header file is included in the respective target source
code files.


## Compiling the generated output
------------------------------
Before executing the instrumented version of the target program, the generated
runtime monitor must be compiled along with the target program using the
following command:

`gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c`


## Manually run intermediate generation steps
------------------------------------------
[Grako](https://pythonhosted.org/grako/), a PEG parser generator, is used to
generate the SMEDL and PEDL parsers for their EBNF-defined grammars.

To generate a SMEDL parser using the grammar:

	  grako smedl/parser/smedl.grako -o smedl/parser/smedl_parser.py
	( grako      GRAMMAR             -o     OUTPUT_PARSER  )

To parse a SMEDL file using the generated parser:

      python smedl/parser/smedl_parser.py example.smedl object
    ( python      PARSER                   INPUT_FILE   START_RULE )

(Use '-t' command-line option to enable debug tracing)

## Compile with architecture description
--------------------------------------

An architecture description file can be compiled with the SMEDL specification
using the command `python -m smedl.mgen PEDL_SMEDL_FILENAME --arch=ARCH_SMEDL_FILENAME`.
Note that `ARCH_SMEDL_FILENAME` does not contain '.a4smedl' suffix.

Moreover, it is necessary to compile separately with corresponding SMEDL
specifications. For more info, readers can refer to the document Architecture_Description_Language_for_SMEDL.

## Running the test suite
--------------------------------------
You may run the tool's test suite by simply calling `nosetests` from the
project's root directory.

## Updating from the repository
----------------------------
The canonical repository for this project is located on the
[PRECISE GitLab](https://gitlab.precise.seas.upenn.edu/pgebhard/smedl).

At the moment, this is an internal repository, so please contact
[Peter Gebhard](pgeb@seas.upenn.edu) for access.
