#include <stdexcept>
#include "ros/ros.h"
#include "{{syncset}}_ros.h"

extern "C" {
    #include "smedl_types.h"
    #include "{{syncset}}_global_wrapper.h"
}

namespace SMEDL {
    {{syncset}}Node *{{syncset}}Node::callback_node = NULL;

    /* Establishes callbacks with SMEDL and ROS and begin interfacing
     * between them.
     *
     * You must not construct a second instance before the first is
     * destroyed! */
    {{syncset}}Node::{{syncset}}Node() {
        attach_global_wrapper();
        // Let node_handle be initialized by the default constructor

        // Advertise topics for events exported from this synchronous set
        {% for decl in mon_decls %}
        {% for conn in decl.inter_connections %}
        pub_{{conn.channel}} = node_handle.advertise<{{conn.channel}}MsgType>({{conn.channel}}_ros_topic, queue_size);
        {% endfor %}
        {% endfor %}

        // Subscribe to topics imported into this synchronous set
        {% for conn in sys.imported_channels(syncset) %}
        sub_{{conn.channel}} = node_handle.subscribe({{conn.channel}}_ros_topic, queue_size, &{{syncset}}Node::ros_cb_{{conn.channel}}, this);
        {% endfor %}
    }

    /* Unsubscribe and stop interfacing between ROS and SMEDL and
     * clean up resources */
    {{syncset}}Node::~{{syncset}}Node() {
        // Free global wrapper and unregister callbacks if they are assigned
        // to us
        detach_global_wrapper();

        // Destruction of pub_*/sub_* members will unannounce/unsubscribe
    }

    /* Callback functions for SMEDL global wrapper */
    {% for decl in mon_decls %}
    {% for conn in decl.inter_connections %}
    void {{syncset}}Node::smedl_cb_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux) {
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
            return;
        }
        msg.SMEDL_{{conn.channel}}_ID{{loop.index0}} = ptr_str;
        {% elif param is sameas SmedlType.STRING %}
        {% unsupported "'thread' type cannot be transported over ROS" %}
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
            return;
        }
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}} = ptr_str;
        {% elif param is sameas SmedlType.STRING %}
        {% unsupported "'thread' type cannot be transported over ROS" %}
        {% elif param is sameas SmedlType.OPAQUE %}
        msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}}.insert(
            msg.SMEDL_{{conn.channel}}_PARAM{{loop.index0}}.end(),
            params[{{loop.index0}}].v.o.data,
            params[{{loop.index0}}].v.o.data + params[{{loop.index0}}].v.o.size)
        {% endif %}
        {% endfor %}

        // Publish the message
        callback_node->pub_{{conn.channel}}.publish(msg);
    }
    {% endfor %}
    {% endfor %}

    /* Callback functions for ROS subscriptions */
    {% for conn in sys.imported_channels(syncset) %}
    void {{syncset}}Node::ros_cb_{{conn.channel}}(const {{conn.channel}}MsgType::ConstPtr &msg) {
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
        {% elif param is sameas SmedlType.THREAD %}
        {% unsupported "'thread' type cannot be transported over ROS" %}
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
        {% elif param is sameas SmedlType.THREAD %}
        {% unsupported "'thread' type cannot be transported over ROS" %}
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
        import_{{syncset}}_{{conn.channel}}(identities, params, NULL);
    }
    {% endfor %}

    /* Do all SMEDL initialization and attach this instance to the global
     * wrapper callbacks. */
    void {{syncset}}Node::attach_global_wrapper() {
        if (callback_node != NULL) {
            throw std::logic_error("Cannot attach multiple nodes to one "
                "global wrapper simultaneously");
        }

        // Direct callbacks to this instance
        callback_node = this;

        // Initialize the synchronous set
        init_{{syncset}}_syncset();

        // Set callbacks
        {% for decl in mon_decls %}
        {% for conn in decl.inter_connections %}
        callback_{{syncset}}_{{conn.channel}}(smedl_cb_{{conn.channel}});
        {% endfor %}
        {% endfor %}
    }

    /* If this instance is currently attached to the global wrapper callbacks,
     * detach them and deinitialize the global wrapper. This is called by the
     * destructor, so there is generally no need to call it manually. */
    void {{syncset}}Node::detach_global_wrapper() {
        if (callback_node == this) {
            // Free the global wrapper, which also detaches callbacks
            free_{{syncset}}_syncset();
            callback_node = NULL;
        }
    }
}

int main(int argc, char **argv) {
    ros::init(argc, argv, "{{syncset}}_node");
    SMEDL::{{syncset}}Node smedl_node;
    ros::spin();
}
