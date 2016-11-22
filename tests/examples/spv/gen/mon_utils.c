#include <stdio.h>
#include <stdlib.h>
#include "mon_utils.h"
#include "cJSON.h"

void output_config_error(config_t cfg) {
    fprintf(stderr, "%s:%d - %s\n", config_error_file(&cfg),
        config_error_line(&cfg), config_error_text(&cfg));
    config_destroy(&cfg);
    exit(EXIT_FAILURE);
}

void raise_error(char *scen, const char *state, char *action, char *type) {
    printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}\n", scen, state, action, type);
}