// vim: set ft=cpp :

/******************************************************************************
 * ROS Configuration for {{sys.name}} SMEDL Nodes
 *
 * This file allows you to configure the topics, message types, and fields
 * used for each SMEDL connection and certain other parameters affecting the
 * SMEDL nodes.
 *
 * To change the message type used for a particular SMEDL connection:
 * 1. Update the typedef and field names below (and potentially the topic name)
 * 2. Update the #includes below
 * 3. If the chosen message type is in a different ROS package, update the
 *    dependencies for this package:
 *    a. Add a <depend> tag to smedl_{{sys.name}}/package.xml,
 *       for example:
 *
 *       <depend>std_msgs</depend>
 *
 *    b. Add the package to the "find_package(catkin ...)" command in
 *       smedl_{{sys.name}}/CMakeLists.txt, for example:
 *
 *       find_package(catkin REQUIRED COMPONENTS
 *         roscpp
 *         message_generation
 *         std_msgs)
 ******************************************************************************/

#ifndef SMEDL_{{sys.name}}_ROS_CONFIG_INC
#define SMEDL_{{sys.name}}_ROS_CONFIG_INC

/*
 * All headers for message types used for SMEDL events must be included here.
 */
{% for conn in inbound_connections %}
#include "smedl_{{sys.name}}/{{conn.channel}}Msg.h"
{% endfor %}
{% for conn in internal_connections %}
#include "smedl_{{sys.name}}/{{conn.channel}}Msg.h"
{% endfor %}
{% for conn in outbound_connections %}
#include "smedl_{{sys.name}}/{{conn.channel}}Msg.h"
{% endfor %}

/*
 * For each SMEDL connection, the following can be configured:
 *
 * - Topic to publish/subscribe to:
 *
 *   std::string <connection>_ros_topic = ...;
 *
 * - ROS message type to use:
 *
 *   typedef ... <connection>MsgType;
 *
 * - Field names from that message type to use for each event parameter:
 *
 *   #define SMEDL_<connection>_PARAM0 ...
 *   #define SMEDL_<connection>_PARAM1 ...
 *   ...
 *
 * - Field names from the message type to use for each monitor identity (only
 *   used for outbound and internal connections):
 *
 *   #define SMEDL_<connection>_ID0 ...
 *   #define SMEDL_<connection>_ID1 ...
 *   ...
 */

namespace SMEDL {
    {% if inbound_connections is nonempty %}
    /*
     * Inbound connections: SMEDL events coming from non-SMEDL nodes
     */
    {% for conn in inbound_connections %}

    const std::string {{conn.channel}}_ros_topic = "/smedl/{{sys.name}}/channels/{{conn.channel}}";
    typedef smedl_{{sys.name}}::{{conn.channel}}Msg {{conn.channel}}MsgType;
    {% for param in conn.source_event_params %}
    {% if param is not none %}
    #define SMEDL_{{conn.channel}}_PARAM{{loop.index0}} param{{loop.index0}}
    {% endif %}
    {% endfor %}
    {% endfor %}

    {% endif %}
    {% if outbound_connections is nonempty %}
    /*
     * Outbound connections: SMEDL events meant to go to non-SMEDL nodes
     */
    {% for conn in outbound_connections %}

    const std::string {{conn.channel}}_ros_topic = "/smedl/{{sys.name}}/channels/{{conn.channel}}";
    typedef smedl_{{sys.name}}::{{conn.channel}}Msg {{conn.channel}}MsgType;
    {% for param in conn.source_event_params %}
    {% if param is not none %}
    #define SMEDL_{{conn.channel}}_PARAM{{loop.index0}} param{{loop.index0}}
    {% endif %}
    {% endfor %}
    {% for param in conn.source_mon.params %}
    {% if param is not none %}
    #define SMEDL_{{conn.channel}}_ID{{loop.index0}} id{{loop.index0}}
    {% endif %}
    {% endfor %}
    {% endfor %}

    {% endif %}
    {% if internal_connections is nonempty %}
    /*
     * Internal connections: SMEDL events from one SMEDL node to another SMEDL
     * node (There is likely no reason to change these.)
     */
    {% for conn in internal_connections %}

    const std::string {{conn.channel}}_ros_topic = "/smedl/{{sys.name}}/channels/{{conn.channel}}";
    typedef smedl_{{sys.name}}::{{conn.channel}}Msg {{conn.channel}}MsgType;
    {% for param in conn.source_event_params %}
    {% if param is not none %}
    #define SMEDL_{{conn.channel}}_PARAM{{loop.index0}} param{{loop.index0}}
    {% endif %}
    {% endfor %}
    {% for param in conn.source_mon.params %}
    {% if param is not none %}
    #define SMEDL_{{conn.channel}}_ID{{loop.index0}} id{{loop.index0}}
    {% endif %}
    {% endfor %}
    {% endfor %}

    {% endif %}
    /* Number of messages that can be awaiting publishing for a given topic
     * before further messages will be dropped */
    const uint32_t queue_size = 1000;
}

#endif
