#include "smedl_types.h"

{% for conn, targets in sys.imported_channels(syncset) %}
{% for target in targets if target.target_type == 'export' %}
int perform_{{target.mon_string}}_{{target.event}}(SMEDLValue *ids, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}
