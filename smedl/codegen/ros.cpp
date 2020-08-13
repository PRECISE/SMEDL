#include <stdexcept>
#include "ros/ros.h"

extern "C" {
    #include "{{syncset}}_global_wrapper.h"
}

//TODO Move to .h eventually
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

            /* Do all SMEDL initialization (if not already done) and attach
             * this instance to the global wrapper callbacks. Return true/false
             * for success/failure. */
            bool attach_global_wrapper();
            /* If this instance is currently attached to the global wrapper
             * callbacks, detach them and deinitialize the global wrapper. */
            bool detach_global_wrapper();

            /* Callback functions for SMEDL global wrapper */
            {% for decl in mon_decls %}
            {% for conn in decl.inter_connections %}
            static void smedl_cb_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux);
            {% endfor %}
            {% endfor %}

            /* Callback functions for ROS subscriptions */
            {% for conn in sys.imported_channels(syncset) %}
            void ros_cb_{{conn.channel}}(/*TODO*/);
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

namespace SMEDL {
    #include "{{syncset}}_ros_config.inc"

    {{syncset}}Node::callback_node = NULL;

    /* Establishes callbacks with SMEDL and ROS and begin interfacing
     * between them.
     *
     * You must not construct a second instance before the first is
     * destroyed! */
    {{syncset}}Node::{{syncset}}Node(int argc, char **argv) {
        attach_global_wrapper();
        // Let node_handle be initialized by the default constructor

        ros::init(argc, argv, "/smedl/{{sys.name}}/{{syncset}}_node");

        // Advertise topics for events exported from this synchronous set
        {% for decl in mon_decls %}
        {% for conn in decl.inter_connections %}
        pub_{{conn.channel}} = node_handle.advertise</*TODO*/>({{conn.channel}}_ros_topic, queue_size);
        {% endfor %}
        {% endfor %}

        // Subscribe to topics imported into this synchronous set
        {% for conn in sys.imported_channels(syncset) %}
        sub_{{conn.channel}} = node_handle.subscribe({{conn.channel}}_ros_topic, queue_size, ros_cb_{{conn.channel}}, this);
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
    {{syncset}}Node::smedl_cb_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux) {
        //TODO Send a message for this channel using instance callback_node
    }
    {% endfor %}
    {% endfor %}

    /* Do all SMEDL initialization (if not already done) and attach
     * this instance to the global wrapper callbacks. Return true/false
     * for success/failure. */
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
        callback_{{syncset}}_{{conn.channel}}(cb_{{conn.channel}});
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
    SMEDL::SMEDL{{syncset}}Node smedl_node(argc, argv);
    //TODO anything else?
}
