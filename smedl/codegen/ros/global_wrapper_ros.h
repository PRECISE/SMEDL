#ifndef {{syncset}}_GLOBAL_WRAPPER_ROS_H
#define {{syncset}}_GLOBAL_WRAPPER_ROS_H

#include "{{syncset}}_node.h"

extern "C" {
    #include "smedl_types.h"
}

namespace SMEDL {
    class {{syncset}}GlobalWrapper {
        private:
            /* The {{syncset}}Node instance used for callbacks. Set in the
             * constructor and reset to nullptr in the destructor. */
            static {{syncset}}Node *callback_node;

            /* Callback functions for SMEDL global wrapper */
            {% for decl in mon_decls %}
            {% for conn in decl.inter_connections %}
            static int cb_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux);
            {% endfor %}
            {% endfor %}
        public:
            {{syncset}}GlobalWrapper({{syncset}}Node *cb_node);
            {{syncset}}GlobalWrapper(const {{syncset}}GlobalWrapper&) = delete;
            {{syncset}}GlobalWrapper & operator=(
                    const {{syncset}}GlobalWrapper&) = delete;
            ~{{syncset}}GlobalWrapper();

            /* Functions to send events to the global wrapper */
            {% for conn in sys.imported_channels(syncset) %}
            int handle_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux) const;
            {% endfor %}
    }
}

#endif
