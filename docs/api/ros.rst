ROS Transport
=============

.. default-domain:: c

.. note::

   Many file names and identifiers in this API contain placeholders for event,
   monitor, and synchronous set names. These placeholders are marked by the use
   of ALLCAPS.

This asynchronous transport sends asynchronous events using ROS topics. Each
synchronous set becomes a ROS node. The output from ``mgen`` in this case is a
ROS package containing all the nodes in the monitoring system. Use the ``-d``
option for ``mgen`` to provide the path to your workspace's ``src/`` directory.

PEDL Events Under ROS
---------------------

The ROS transport was designed under the assumption that PEDL events would
generally be asynchronous, so they could come from or be sent to the rest of
the system via ROS topics. Accordingly, architecture specifications for ROS
will likely want to avoid using the ``pedl``, ``imported``, or ``exported``
keywords in synchronous set definitions.

By default, code for a PEDL node is still generated, but it is disabled in the
``CMakeLists.txt`` and ``SYSNAME.launch`` files.

Message/Topic Configuration
---------------------------

By default, SMEDL generates a message definition for each imported PEDL event
and each exported monitor event and creates a new topic for each one. This is
all configurable, allowing existing ROS topics to be used as the source for
PEDL events and the destination for exported monitor events.

All of this configuration resides in ``SYSNAME_ros_config.inc``, a special C++
source code file that gets included in each node. This file contains
instructions for changing the message type and topic for a particular event, as
well as the message fields used to represent each source event parameter and
each source monitor identity.

The type of each field used as an event parameter or monitor identity should
match the appropriate SMEDL type:

=========== ===================================================================
SMEDL Type  ROS Type
=========== ===================================================================
``int``     ``int32``
``char``    ``uint8``
``float``   ``float64``
``string``  ``string``
``pointer`` ``string`` (by converting to ``uintptr_t`` in C++ and then
            rendering that in hexadecimal)
``opaque``  ``uint8[]``
=========== ===================================================================
