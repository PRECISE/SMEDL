#ifndef {{syncset}}_ROS_H
#define {{syncset}}_ROS_H

#include "ros/ros.h"
#include "{{sys.name}}_ros_config.inc"

extern "C" {
    #include "smedl_types.h"
}

namespace SMEDL {
    class {{syncset}}Node {
        private:
            /* The instance used for callbacks. Set by attach_global_wrapper().
             * If NULL, the global wrapper is not yet initialized. */
            static {{syncset}}Node *callback_node;

            /* NodeHandle for this node */
            ros::NodeHandle node_handle;

            /* Publishers for channels exported from this synchronous set */
            {% for decl in mon_decls %}
            {% for conn in decl.inter_connections %}
            ros::Publisher pub_{{conn.channel}};
            {% endfor %}
            {% endfor %}

            /* Subscribers for channels imported into this synchronous set */
            {% for conn in sys.imported_channels(syncset) %}
            ros::Subscriber sub_{{conn.channel}};
            {% endfor %}

            /* Do all SMEDL initialization and attach this instance to the
             * global wrapper callbacks. */
            void attach_global_wrapper();
            /* If this instance is currently attached to the global wrapper
             * callbacks, detach them and deinitialize the global wrapper. */
            void detach_global_wrapper();

            /* Callback functions for SMEDL global wrapper */
            {% for decl in mon_decls %}
            {% for conn in decl.inter_connections %}
            static void smedl_cb_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux);
            {% endfor %}
            {% endfor %}

            /* Callback functions for ROS subscriptions */
            {% for conn in sys.imported_channels(syncset) %}
            void ros_cb_{{conn.channel}}(const {{conn.channel}}MsgType::ConstPtr &msg);
            {% endfor %}
        public:
            /* Establishes callbacks with SMEDL and ROS and begin interfacing
             * between them.
             *
             * You must not construct a second instance before the first is
             * destroyed! */
            {{syncset}}Node(int argc, char **argv);
            /* Unsubscribe and stop interfacing between ROS and SMEDL and
             * clean up resources */
            ~{{syncset}}Node();
            /* Cannot make copies, as only one instance can interface with the
             * global wrapper at a time. */
            {{syncset}}Node(const {{syncset}}Node &other) = delete;
            {{syncset}}Node & operator=(const {{syncset}}Node &other) = delete;
    };
}

#endif
