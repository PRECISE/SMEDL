#include <stdexcept>
#include "{{syncset}}_node.h"
#include "{{syncset}}_global_wrapper_ros.h"

extern "C" {
    #include "smedl_types.h"
    #include "{{syncset}}_global_wrapper.h"
}

namespace SMEDL {
    {{syncset}}Node *{{syncset}}Node::callback_node = nullptr;

    {{syncset}}GlobalWrapper::{{syncset}}GlobalWrapper({{syncset}}Node *cb_node) {
        // Can only have one {{syncset}}GlobalWrapper at a time
        if (callback_node != NULL) {
            throw std::logic_error("Cannot attach to one global wrapper "
                "multiple times simultaneously");
        }

        // Initialize the synchronous set
        if (!init_{{syncset}}_syncset()) {
            //TODO This should potentially be some other exception
            throw std::bad_alloc("Could not initialize global wrapper");
        }

        // Direct callbacks to this instance
        callback_node = cb_node;

        // Set callbacks
        {% for decl in mon_decls %}
        {% for conn in decl.inter_connections %}
        callback_{{syncset}}_{{conn.channel}}(cb_{{conn.channel}});
        {% endfor %}
        {% endfor %}
    }

    {{syncset}}GlobalWrapper::~{{syncset}}GlobalWrapper() {
        free_{{syncset}}_syncset();
        callback_node = NULL;
    }

    /* Callback functions for SMEDL global wrapper */
    {% for decl in mon_decls %}
    {% for conn in decl.inter_connections %}
    int {{syncset}}GlobalWrapper::cb_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux) {
        return callback_node->send_{{conn.channel}}(ids, params, *aux);
    }
    {% endfor %}
    {% endfor %}

    /* Functions to send events to the global wrapper */
    {% for conn in sys.imported_channels(syncset) %}
    int {{syncset}}GlobalWrapper::handle_{{conn.channel}}(SMEDLValue *ids, SMEDLValue *params, void *aux) const {
        return import_{{syncset}}_{{conn.channel}}(ids, params, aux);
    }
    {% endfor %}
}
