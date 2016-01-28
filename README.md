# SMEDL/PEDL Monitor Generator
### Version 1.0

## Requirements
--------------
1. [Python 3](https://docs.python.org/3/)
2. [pip](https://pip.pypa.io/en/stable/)
    - [Grako 3.6](https://pythonhosted.org/grako/)
    - [Jinja2 2.8](http://jinja.pocoo.org/)

## Getting started
---------------
A [Python virtual environment](https://virtualenv.readthedocs.org/en/latest/) including 
[Python 3](https://docs.python.org/3/) and all required Python packages has been defined 
to simplify the process of getting started with the tool.

To setup the virtual environment, run the following command from the project's root 
directory:

`pyvenv .env && source .env/bin/activate && pip install -r requirements.txt`

NOTE: If you choose to not use the virtual environment, you can simply install the 
required Python packages using the following command:

`pip install -r requirements.txt`


## Generating the monitor
----------------------
The 'mgen' script is the primary interface for generating software monitors from SMEDL and 
PEDL definitions. This script can be run with the following command (from the src/ 
directory):

`./mgen.py PEDL_SMEDL_FILENAME`

This script will generate C source code representing a runtime monitor as specified by the 
PEDL and SMEDL definitions, along with necessary monitor management infrastructure.

To allow the script to properly locate the PEDL and SMEDL files, the script's single 
parameter should be the name used by the PEDL and SMEDL files, and that name should be 
identical for both files except for their file extensions, .pedl and .smedl.

Note: There are two debug flags that can be specified at the command-line. These are the
'-s' flag for displaying the contents of internal data structures used by the monitor 
during its generation steps and the '-d' flag for outputting various debug statements 
written in the monitor generator code.


## Instrumenting the target
------------------------
At the moment, instrumentation of the target program must be performed manually. The 
generated event handling functions, or 'probes', can be found in the {object}\_mon.h file. 
The probe naming convention uses the monitor object name and the event name, separated by 
an underscore. Probes can be added anywhere in the target program (assuming the PEDL 
definitions are followed) and will be compiled with the target if the expected parameters 
are provided and the {object}\_mon.h header file is included in the respective target 
source code files.


## Compiling the generated output
------------------------------
Before executing the instrumented version of the target program, the generated runtime 
monitor must be compiled along with the target program using the following command:

`gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c`

    // TODO: Update this to use a generated Makefile
    // New command would simply be: make


## Manually run intermediate generation steps
------------------------------------------
[Grako](https://pythonhosted.org/grako/), a PEG parser generator, is used to generate the
SMEDL and PEDL parsers for their EBNF-defined grammars.

To generate a SMEDL parser using the grammar:

	  grako parser/smedl.grako -o parser/smedl_parser.py
	( grako      GRAMMAR       -o     OUTPUT_PARSER  )

To parse a SMEDL file using the generated parser:

      python parser/smedl_parser.py example.smedl  object
    ( python     PARSER              INPUT_FILE   START_RULE )

(Use '-t' command-line option to enable debug tracing)


## Updating from the repository
----------------------------
The canonical repository for this project is located at 
[SMEDL](https://gitlab.precise.seas.upenn.edu/pgebhard/smedl).

At the moment, this is an internal repository, so please contact 
[Peter Gebhard](pgeb@seas.upenn.edu) for access.


## Changelog
---------
1.0: (August 6, 2015)
    - PUT FEATURES HERE