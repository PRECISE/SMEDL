#SMEDL/PEDL Monitor Generator
###Version 1.0

##Requirements
--------------
1. [Python 3](https://docs.python.org/3/)
2. [pip](https://pip.pypa.io/en/stable/)
    - [Grako 3.6](https://pythonhosted.org/grako/)
    - [Jinja2 2.8](http://jinja.pocoo.org/)

##Getting started
---------------
A [Python virtual environment](https://virtualenv.readthedocs.org/en/latest/) including [Python 3.4.3](https://docs.python.org/3.4/index.html) and all required Python packages has been created to simplify the process of getting started with the tool.

To setup the virtual environment, run the following command from the project's root directory:

    pyvenv .env && source .env/bin/activate && pip install -r requirements.txt

NOTE: If you choose to not use the virtual environment, you can simply install the required Python packages using the following command:

    pip install -r requirements.txt


##Generating the monitor
----------------------
The 'mgen' script is the primary interface for generating software monitors from SMEDL and PEDL definitions. This script can be run with the following command:

    python src/mgen.py PEDL_FILE SMEDL_FILE

This script will generate C source code representing a runtime monitor as specified by the PEDL and SMEDL definitions, along with necessary monitor management infrastructure.


##Instrumenting the target
------------------------
At the moment, instrumentation of the target program must be performed manually. The generated event handling functions, or 'probes', can be found in the {object}\_mon.h file. The probe naming convention uses the monitor object name and the event name, separated by an underscore. Probes can be added anywhere in the target program (assuming the PEDL definitions are followed) and will be compiled with the target if the expected parameters are provided and the {object}\_mon.h header file is included in the respective target source code files.


##Compiling the generated output
------------------------------
Before executing the instrumented version of the target program, the generated runtime monitor must be compiled along with the target program using the following command:

	gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c

    // TODO: Update this to use a generated Makefile
    // New command would simply be: make


##Manually run intermediate generation steps
------------------------------------------
[Grako](https://pythonhosted.org/grako/), a PEG parser generator, is used to generate the SMEDL and PEDL parsers for their EBNF-defined grammars.

To generate a SMEDL parser using the grammar:

	  grako smedl.grako -o smedl_parser.py
	( grako   GRAMMAR   -o  OUTPUT_PARSER  )

To parse a SMEDL file using the generated parser:

      python smedl_parser.py example.smedl  object
    ( python     PARSER       INPUT_FILE  START_RULE )

(Use '-t' command-line option to enable debug tracing)


##Updating from the repository
----------------------------
SHOULD WE POST THIS PROJECT ON GITHUB?


##Changelog
---------
1.0: (August 6, 2015)
    - PUT FEATURES HERE