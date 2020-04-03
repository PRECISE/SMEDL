#ifndef MON_UTILS_H
#define MON_UTILS_H

{% if genjson -%}
#include <libconfig.h>

typedef struct smedl_provenance_t {
     char event[255];
     unsigned int line;
     unsigned long trace_counter;
}smedl_provenance_t;

void output_config_error(config_t cfg);
{% endif -%}
void raise_error(char*, const char*, char*, char*);

#endif
