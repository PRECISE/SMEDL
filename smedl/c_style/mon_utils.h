#ifndef MON_UTILS_H
#define MON_UTILS_H

#include <libconfig.h>

void output_config_error(config_t cfg);
void raise_error(char*, const char*, char*, char*);

#endif
