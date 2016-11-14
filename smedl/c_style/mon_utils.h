#ifndef MON_UTILS_H
#define MON_UTILS_H

#include <libconfig.h>
#include "cJSON.h"

void output_config_error(config_t cfg);
void raise_error(char*, const char*, char*, char*);
cJSON* buildFrameCheck(char*, int, cJSON*);
cJSON* parseFrameCheck(cJSON*);

#endif
