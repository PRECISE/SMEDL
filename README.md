# SMEDL/PEDL Monitor Generator
### Version 1.0.0

## Requirements
1. [Python 3.5](https://docs.python.org/3.5/index.html)
2. [pip](https://pip.pypa.io/en/stable/)
    - [Grako 3.14](https://pythonhosted.org/grako/)
    - [Jinja2 2.8](http://jinja.pocoo.org/)
    - [nose 1.3.7](https://nose.readthedocs.io/en/latest/)
    - [pika 0.10.0](https://pika.readthedocs.io/en/0.10.0/index.html)
    - [pylibconfig2 0.2.5](https://pypi.python.org/pypi/pylibconfig2/0.2.5)
    - [pyparsing](https://pypi.python.org/pypi/pyparsing/2.1.10)

## Getting started
A [Python virtual environment](https://docs.python.org/3/library/venv.html)
including [Python 3.5](https://docs.python.org/3.5/index.html) and all required Python
packages has been defined to simplify the process of getting started with the
tool.

If you want to use a virtual environment (recommended), set it up by running
the following command from the project's root directory:

    pyvenv-3.5 .env && source .env/bin/activate

To install all of the required dependencies from PyPi and install the monitor
generator `mgen` as an executable on your path, run the following command in
the root of the repository:

    pip install .

To update the installation of `mgen` without updating its dependencies, run

    pip uninstall smedl
    pip install .


## Generating the monitor
The 'mgen' script is the primary interface for generating software monitors
from SMEDL and PEDL definitions. This script can be run with the following
command (from the project root directory):

    mgen PEDL_SMEDL_FILENAME

This script will generate C source code representing a runtime monitor as
specified by the PEDL and SMEDL definitions, along with necessary monitor
management infrastructure.

To allow the script to properly locate the PEDL and SMEDL files, the script's
single parameter should be the name used by the PEDL and SMEDL files, and that
name should be identical for both files except for their file extensions,
`.pedl` and `.smedl`.

Note: There are two debug flags that can be specified at the command-line.
These are the '-s' flag for displaying the contents of internal data structures
used by the monitor during its generation steps and the '-d' flag for
outputting various debug statements written in the monitor generator code.

Other useful flags:
      --version : The current mgen version number
      --helper <HEADER FILE> : Include the specified header file for providing helper functions
      --console : Forces output to only show in the console; no file output will be generated
      --noimplicit : Disables implicit error handling in the generated monitor
      --arch <ARCH FILE> : The name of architechture file to parse (Described further below)
      --dir <DIRECTORY> : Output the generated files to this directory relative to the input files



## Instrumenting the target
At the moment, instrumentation of the target program must be performed
manually. The generated event handling functions, or 'probes', can be found in
the {object}\_mon.h file. The probe naming convention uses the monitor object
name and the event name, separated by an underscore. Probes can be added
anywhere in the target program (assuming the PEDL definitions are followed) and
will be compiled with the target if the expected parameters are provided and
the {object}\_mon.h header file is included in the respective target source
code files.


## Compiling the generated output
Before executing the instrumented version of the target program, the generated
runtime monitor must be compiled along with the target program using the
following command:

gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c

Note: If the monitor is an asynchronous monitor, the file {{base_file_name}}_monitor_wrapper.c will be generated, which should be added to the gcc command.


## Manually run intermediate generation steps
[Grako](https://pythonhosted.org/grako/), a PEG parser generator, is used to
generate the SMEDL and PEDL parsers for their EBNF-defined grammars.

To generate a SMEDL parser using the grammar:

	  grako smedl/parser/smedl.grako -o smedl/parser/smedl_parser.py
	( grako      GRAMMAR             -o     OUTPUT_PARSER  )

To parse a SMEDL file using the generated parser:

      python smedl/parser/smedl_parser.py example.smedl object
    ( python      PARSER                   INPUT_FILE   START_RULE )

(Use the `-t` command-line option to enable debug tracing)


## RabbitMQ
Asynchronous monitoring of events has been implemented using the [Advanced Message Queuing Protocol](http://www.amqp.org/) by the [RabbitMQ](https://www.rabbitmq.com/) message broker.

### Configuring a RabbitMQ-enabled monitor
**Hostname**: The host address of your RabbitMQ broker.

**Port**: Keep this value as `5672` if your broker is using the default port, or set it to the custom port you have already configured for your broker.

**Username**: Your username for the broker.

**Password**: Your password for the broker.

**Exchange**: The main event-handling message exchange.

**Control Exchange (ctrl_exchange)**: The message exchange for passing control-related messages.

###### Example SMEDL RabbitMQ configuration file
	rabbitmq =
	{
		hostname = "example.com";
		port = 5672;
		username = "test-user";
		password = "test-password";
		exchange = "example.topic";
		ctrl_exchange = "example.control";
	};

### Format of routing key
The formal of the routing key contains four parts: the channel name, the list of identities of the monitor instance, the event name and the list of attributes of the event. Each element(including channel name, event name, each identity or attribute value) is divided by character '.'. Note that if the type of the attributes of events or identities of the monitor is not typed with integer, it will be replaced by "0" as a place holder. (Note that the string can not be the id of the monitor for now, which will be implemented in the next released version). 

###### Example of routing key format
There are two monitors RateComputation(int) and ThresholdCrossDetection(int) communicating with each other through event dataUpdate2(string, float, float),defined in channel "ch1". For the monitor instances RateComputation(0) and ThresholdCrossDetection(0), the format of the routing key sent along with the message will be "ch1.0.dataUpdates2.0.0.0". The first "0" in the routing key represents the id of RateComputation. The other three "0"s represent the place holder for three  attributes of the event dataUpdate2.  

### JSON format of the asynchronous event message
    {
      "name" : "eventName",
      "fmt_version" : "format version",
      "params": {
                  "v1" : value1,
              "v2" : value2,
              ...
      }
      "provenance" :{
            ...
      }
    }

Only the message is encoded in JSON string and the routing key still follows the format of the rabbitmq. As a result, the  field "name" in the JSON string is not used for now. Moreover, the field "params" is optional when there is no attribute in the event. Names in the "params" field are "v"+index where index is from 1. Types and order of the data in "params" follows the definition of the event. The option field "provenance" contains the provenance information, which is opaque to the monitor. 


## Compiling with an architecture description
An architecture description file can be compiled with the SMEDL specification
using the following command:

    mgen PEDL_SMEDL_FILENAME --arch=ARCH_SMEDL_FILENAME

Note that `ARCH_SMEDL_FILENAME` does not contain the `.a4smedl` suffix.

Moreover, it is necessary to compile separately with corresponding SMEDL
specifications. For more info, readers can refer to the document ``Architecture_Description_Language_for_SMEDL``.

## State variable initialization
Default initial value of state variables can be specified in the SMEDL specification:

    Object mon
    state
    int i = 0, j=3;
    string s = "abc";
    double d = -2.5;
    ...

## Dynamic instantiation
In the architecture file, a modifier "creation" can be added before imported events of the monitor:

    System Tracking :=
    Async RateComputation(int, string)
    {
        imported creation dataUpdate (int, string,float,float);
        imported timeout();
        imported end();
        exported dataUpdate2(string, float, float);
    }
    ...
    ch3: dataUpdate => RateComputation.dataUpdate {RateComputation[0]=dataUpdate[0];RateComputation[1]=dataUpdate[1]}

For the example above, instance of RateComputation can be created whenever an dataUpdate event is received. However, in the pattern specification, all identifiers should be bounded. Moreover, target monitor should always appear at the left side of the connection pattern expression. 

## Synchronous Communication

Related monitors can be grouped into a "synchronous set." Monitors in the same synchronous set all run in one combined process. They use direct calls to each other's event handlers rather than RabbitMQ messages to exchange events between each other.

This comes with syntax changes in the architecture file and additional C source files that will be generated with the monitors.

### New changes to the architecture file

* Monitors are now declared with the `Monitor` keyword rather than the `Async` keyword. For example:
  
    ```
    Monitor RateComputation(int, string)
    {
        imported creation dataUpdate (int, string,float,float);
        imported timeout();
        imported end();
        exported dataUpdate2(string, float, float);
    }
    ```

* Between the monitor declarations and the channel specifications, there is a new section where synchronous sets are defined. It begins with the line `Synchronous sets:` followed by the list of synchronous sets. Each set is specified with its name, followed by a comma-separated list of monitor names enclosed in curly braces. For example, to define a set named "metricsSet" containing the monitors "frontend" and "metricsCollector":

    ```
    Synchronous sets:
    metricsSet: {frontend, metricsCollector}
    ```

* Finally, the start of the channel specifications must be maked with the line `Channels:` to separate it from the synchronous set definitions. Buiding on the previous example:

    ```
    Synchronous sets:
    metricsSet: {frontend, metricsCollector}

    Channels:
    ch1: measurement => frontend.measurementIn
    ch2: frontend.requestMetrics => metricsCollector.metricsRequest
    ...
    ```

**An example monitor using the new syntax and features can be found in tests/examples/multi-moving-average.**

### Additional C source files

With this change to mgen, the wrapper from dynamic instantiation gets replaced with a "local wrapper" and "global wrapper." The local wrapper shares the same name as the old wrapper from dynamic instantiation (`<monitor>_wrapper.c`/`.h`), though the contents are very different. The global wrapper (`<set_name>_global_wrapper.c`/`.h`) is an entirely new file.

There is one global wrapper per synchronous set and it routes all events between monitors and takes on the role of interfacing with RabbitMQ. The local wrapper is the interface between the global wrapper and individual monitor instances. It handles dynamic instantiation and distributing imported events to the correct instances of its monitor.

### Generating and building synchronous monitors

The steps for generating monitors have not changed. Run mgen the same way as before. The new wrappers will be generated automatically if the architecture file is provided. Note that the global wrapper is generated any time an architecture file is given, but the produced .c/.h file will be the same for any monitor in the same synchronous set.

When building, there are no new libraries; however, there is the new C file for the global wrapper. The other change is that monitors in the same synchronous set must now all be built (or linked) together. For example, if building the monitors in the `metricsSet` example above:

    gcc -std=c99 -D_POSIX_C_SOURCE=199309L actions.c amqp_utils.c cJSON.c monitor_map.c mon_utils.c frontend_mon.c frontend_monitor_wrapper.c metricsCollector_mon.c metricsCollector_monitor_wrapper.c metricsSet_global_wrapper.c -o metricsSet -lm -lconfig -lrabbitmq

### Synchronous global wrappers

Normally, the global wrapper sends and receives events asynchronously, over RabbitMQ. There is also the option of generating a synchronous interface. In that case, no JSON generation or parsing code is generated either, for performance.

To do this, use the -j or --nojson flag when invoking mgen. The files cJSON.c and amqp_utils.c will not be generated, so be sure to remove these from any makefiles if necessary.

There are two new functions of interest when doing this: `<syncset>_set_init` and `<syncset>_global_import`. These make up the interface between the monitor and the target system.

`<syncset>_set_init()` initializes the internal data structures for the synchronous set's monitors. This function must be called once before any calls to `<syncset>_global_import`.

`<syncset>_global_import(<syncset>_Connection ch_id, param *params)` is what the target system should call to send an event to the monitors in the synchronous set. It takes two parameters:

* `<syncset>_Connection ch_id` is a new enum representing the connections in the architecture file. See \<syncset\>_global_wrapper.h to see how it is defined. Use the connection that corresponds to the event being sent.
* `param *params` is the parameters for the event. See actions.h for more information on this data type.

Currently there is no provision for monitors to export events back to the target system without manual modifications. Until such a feature is discussed and implemented, manual modifications should go in the `exported_<monitor>_<eventname>` functions in \<monitor\>_mon.c. These are the functions that get called when the corresponding event is exported from the synchronous set.

## Running the test suite
You may run the tool's test suite by simply calling `nose2` from the
project's root directory.


## Updating from the repository
The canonical repository for this project is located on the
[PRECISE GitLab](https://gitlab.precise.seas.upenn.edu/pgebhard/smedl).

At the moment, this is an internal repository, so please contact
[Peter Gebhard](pgeb@seas.upenn.edu) for access.
