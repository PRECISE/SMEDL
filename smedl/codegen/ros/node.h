#ifndef {{syncset}}_NODE_H
#define {{syncset}}_NODE_H

#include "ros/ros.h"
#include "{{sys.name}}_ros_config.inc"

#include "{{syncset}}_global_wrapper_ros.h"

extern "C" {
    #include "smedl_types.h"
}

namespace SMEDL {
    class {{syncset}}Node {
        private:
            {{syncset}}GlobalWrapper global_wrapper;

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

            /* Callback functions for ROS subscriptions */
            {% for conn in sys.imported_channels(syncset) %}
            void recv_{{conn.channel}}(const {{conn.channel}}MsgType::ConstPtr &msg);
            {% endfor %}
        public:
            /* Establish the {{syncset}}GlobalWrapper and interface
             * between it and ROS.
             * You must not construct a second instance before the first is
             * destroyed! */
            {{syncset}}Node();
            /* Default destructor is sufficient. */
            /* Cannot make copies, as only one instance of
             * {{syncset}}GlobalWrapper can exist at a time. */
            {{syncset}}Node(const {{syncset}}Node &other) = delete;
            {{syncset}}Node & operator=(const {{syncset}}Node &other) = delete;

            /* Functions to send events from the global wrapper */
            {% for decl in mon_decls %}
            {% for conn in decl.inter_connections %}
            int send_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux);
            {% endfor %}
            {% endfor %}

    };
}

#endif
