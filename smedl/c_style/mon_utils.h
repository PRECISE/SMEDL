#ifndef MON_UTILS_H
#define MON_UTILS_H

#include <libconfig.h>
#include "cJSON.h"

typedef struct smedl_provenance_t {
     char event[255];
     unsigned int line;
     unsigned long trace_counter;
}smedl_provenance_t;

void output_config_error(config_t cfg);
void raise_error(char*, const char*, char*, char*);

#endif
