#include <ros/callback_queue.h>
#include <ros/ros.h>
#include "{{syncset}}_node.h"
#include "{{sys.name}}_ros_config.inc"

extern "C" {
    #include "smedl_types.h"
    #include "{{syncset}}_manager.h"
    #include "{{syncset}}_async.h"
}

namespace SMEDL {
    /* The {{syncset}}Node to send and receive all ROS messages through */
    {{syncset}}Node *{{syncset}}_node;

    /* Establish the {{syncset}}GlobalWrapper and interface between
     * it and ROS.
     * You must not construct a second instance before the first is
     * destroyed! */
    {{syncset}}Node::{{syncset}}Node() {
        // Let node_handle be initialized by the default constructor

        // Advertise topics for events exported from this synchronous set
        {% for conn in sys.exported_channels(syncset).keys() %}
        pub_{{conn.channel}} = node_handle.advertise<{{conn.channel}}MsgType>({{conn.channel}}_ros_topic, queue_size);
        {% endfor %}

        // Subscribe to topics imported into this synchronous set
        {% for conn in sys.imported_channels(syncset) %}
        sub_{{conn.channel}} = node_handle.subscribe(
                {{conn.channel}}_ros_topic, queue_size,
                &{{syncset}}Node::recv_{{conn.channel}}, this);
        {% endfor %}
    }

    /* Functions to send events from the global wrapper */
    {% for conn in sys.exported_channels(syncset).keys() %}
    int {{syncset}}Node::send_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux) {
        // Construct the ROS message
        {{conn.channel}}MsgType msg;
        {% if conn.source_mon is not none %}
        {% for param in conn.source_mon.params %}
        {% if param is sameas SmedlType.INT %}
        msg.SMEDL_{{conn.channel}}_ID{{loop.index0}} = ids[{{loop.index0}}].v.i;
        {% elif param is sameas SmedlType.FLOAT %}
        msg.SMEDL_{{conn.channel}}_ID{{loop.index0}} = ids[{{loop.index0}}].v.d;
        {% elif param is sameas SmedlType.CHAR %}
        msg.SMEDL_{{conn.channel}}_ID{{loop.index0}} = ids[{{loop.index0}}].v.c;
        {% elif param is sameas SmedlType.STRING %}
        msg.SMEDL_{{conn.channel}}_ID{{loop.index0}} = ids[{{loop.index0}}].v.s;
        {% elif param is sameas SmedlType.POINTER %}
        char ptr_str[40];
        if (!smedl_pointer_to_string(ids[{{loop.index0}}].v.p, ptr_str, 40)) {
            ROS_ERROR("Could not convert pointer to string for sending via ROS");
            return 0;
        }
        msg.SMEDL_{{conn.channel}}_ID{{loop.index0}} = ptr_str;
        {% elif param is sameas SmedlType.OPAQUE %}
        //TODO Revise so that opaque can be any type
        msg.SMEDL_{{conn.channel}}_ID{{loop.index0}}.insert(
            msg.SMEDL_{{conn.channel}}_ID{{loop.index0}}.end(),
            ids[{{loop.index0}}].v.o.data,
            ids[{{loop.index0}}].v.o.data + ids[{{loop.index0}}].v.o.size)
        {% endif %}
        {% endfor %}
        {% endif %}
        {% for param in conn.source_event_params %}
        {% if param is sameas SmedlType.INT %}
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}} = params[{{loop.index0}}].v.i;
        {% elif param is sameas SmedlType.FLOAT %}
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}} = params[{{loop.index0}}].v.d;
        {% elif param is sameas SmedlType.CHAR %}
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}} = params[{{loop.index0}}].v.c;
        {% elif param is sameas SmedlType.STRING %}
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}} = params[{{loop.index0}}].v.s;
        {% elif param is sameas SmedlType.POINTER %}
        char ptr_str[40];
        if (!smedl_pointer_to_string(params[{{loop.index0}}].v.p, ptr_str, 40)) {
            ROS_ERROR("Could not convert pointer to string for sending via ROS");
            return 0;
        }
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}} = ptr_str;
        {% elif param is sameas SmedlType.OPAQUE %}
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}}.insert(
            msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}}.end(),
            params[{{loop.index0}}].v.o.data,
            params[{{loop.index0}}].v.o.data + params[{{loop.index0}}].v.o.size)
        {% endif %}
        {% endfor %}

        // Publish the message
        pub_{{conn.channel}}.publish(msg);
        return 1;
    }
    {% endfor %}

    /* Callback functions for ROS subscriptions */
    {% for conn in sys.imported_channels(syncset) %}
    void {{syncset}}Node::recv_{{conn.channel}}(const {{conn.channel}}MsgType::ConstPtr &msg) {
        // Build identities array
        {% if conn.source_mon is not none and conn.source_mon.params is nonempty %}
        SMEDLValue identities[{{conn.source_mon.params|length}}];
        {% for param in conn.source_mon.params %}
        {% if param is sameas SmedlType.INT %}
        identities[{{loop.index0}}].t = SMEDL_INT;
        identities[{{loop.index0}}].v.i = msg->SMEDL_{{conn.channel}}_ID{{loop.index0}};
        {% elif param is sameas SmedlType.FLOAT %}
        identities[{{loop.index0}}].t = SMEDL_FLOAT;
        identities[{{loop.index0}}].v.d = msg->SMEDL_{{conn.channel}}_ID{{loop.index0}};
        {% elif param is sameas SmedlType.CHAR %}
        identities[{{loop.index0}}].t = SMEDL_CHAR;
        identities[{{loop.index0}}].v.c = msg->SMEDL_{{conn.channel}}_ID{{loop.index0}};
        {% elif param is sameas SmedlType.STRING %}
        identities[{{loop.index0}}].t = SMEDL_CHAR;
        identities[{{loop.index0}}].v.s = msg->SMEDL_{{conn.channel}}_ID{{loop.index0}}.c_str();
        {% elif param is sameas SmedlType.POINTER %}
        identities[{{loop.index0}}].t = SMEDL_POINTER;
        if (!smedl_string_to_pointer(msg->SMEDL_{{conn.channel}}_ID{{loop.index0}}.c_str(), &identities[{{loop.index0}}].v.p)) {
            ROS_ERROR("Could not convert string to pointer (overflow or bad format)");
            return;
        }
        {% elif param is sameas SmedlType.OPAQUE %}
        identities[{{loop.index0}}].t = SMEDL_OPAQUE;
        identities[{{loop.index0}}].v.o.data = &msg->SMEDL_{{conn.channel}}_ID{{loop.index0}}[0];
        identities[{{loop.index0}}].v.o.size = msg->SMEDL_{{conn.channel}}_ID{{loop.index0}}.size();
        {% endif %}
        {% endfor %}
        {% else %}
        SMEDLValue *identities = NULL;
        {% endif %}

        // Build params array
        {% if conn.source_event_params is nonempty %}
        SMEDLValue params[{{conn.source_event_params|length}}];
        {% for param in conn.source_event_params %}
        {% if param is sameas SmedlType.INT %}
        params[{{loop.index0}}].t = SMEDL_INT;
        params[{{loop.index0}}].v.i = msg->SMEDL_{{conn.channel}}_PARAM{{loop.index0}};
        {% elif param is sameas SmedlType.FLOAT %}
        params[{{loop.index0}}].t = SMEDL_FLOAT;
        params[{{loop.index0}}].v.d = msg->SMEDL_{{conn.channel}}_PARAM{{loop.index0}};
        {% elif param is sameas SmedlType.CHAR %}
        params[{{loop.index0}}].t = SMEDL_CHAR;
        params[{{loop.index0}}].v.c = msg->SMEDL_{{conn.channel}}_PARAM{{loop.index0}};
        {% elif param is sameas SmedlType.STRING %}
        params[{{loop.index0}}].t = SMEDL_CHAR;
        params[{{loop.index0}}].v.s = msg->SMEDL_{{conn.channel}}_PARAM{{loop.index0}}.c_str();
        {% elif param is sameas SmedlType.POINTER %}
        params[{{loop.index0}}].t = SMEDL_POINTER;
        if (!smedl_string_to_pointer(msg->SMEDL_{{conn.channel}}_PARAM{{loop.index0}}.c_str(), &params[{{loop.index0}}].v.p)) {
            ROS_ERROR("Could not convert string to pointer (overflow or bad format)");
            return;
        }
        {% elif param is sameas SmedlType.OPAQUE %}
        params[{{loop.index0}}].t = SMEDL_OPAQUE;
        params[{{loop.index0}}].v.o.data = &msg->SMEDL_{{conn.channel}}_PARAM{{loop.index0}}[0];
        params[{{loop.index0}}].v.o.size = msg->SMEDL_{{conn.channel}}_PARAM{{loop.index0}}.size();
        {% endif %}
        {% endfor %}
        {% else %}
        SMEDLValue *params = NULL;
        {% endif %}

        // Send event to SMEDL
        if (!report_{{conn.mon_string}}_{{conn.source_event}}(identities, params, NULL)) {
            ROS_ERROR("Global wrapper failed to process event from {{conn.channel}}");
            return;
        }
    }
    {% endfor %}
}

/* Initialize ROS node.
 *
 * Returns nonzero on success, zero on failure. */
int init_async(void) {
    ros::init(argc, argv, "{{syncset}}_node");
    SMEDL::{{syncset}}_node = new SMEDL::{{syncset}}Node;
}

/* Cleanup ROS node. */
void free_async(void) {
    delete SMEDL::{{syncset}}_node;
}

/* Give the ROS node a change to process messages.
 *
 * If blocking is true, block until a SMEDL event comes, process it, then
 * return. If blocking is false, process all currently pending events and then
 * return.
 *
 * Returns nonzero on success, zero on failure. */
int run_async(blocking) {
    if (blocking) {
        while (ros::ok()) {
            ros::CallOneResult result = ros::getGlobalCallbackQueue()->
                    callOne(ros::WallDuration(0.1));
            if (result == ros::Called) {
                return 1;
            } else if (result == ros::Disabled) {
                return 0;
            }
        }
        /* ROS is shutting down */
        smedl_interrupted = 1;
    } else {
        if (!ros::ok()) {
            /* ROS is shutting down */
            smedl_interrupted = 1;
        }
        ros::getGlobalCallbackQueue()->callAvailable(ros::WallDuration(0));
        return 1;
    }
}

/* Event forwarding functions - Send an asynchronous event from the ROS node.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.exported_channels(syncset).keys() %}

int forward_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    return SMEDL::{{syncset}}_node->send_{{conn.channel}}(identities, params, aux);
}
{% endfor %}
{% if pure_async %}

int main(int argc, char **argv) {
    return c_main(argc, argv);
}
{% endif %}
