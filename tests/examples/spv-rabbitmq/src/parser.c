#include <stdio.h>
#include <stdarg.h>
#include "distance.h"
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <assert.h>

int parse_record(int *time, float *latitude, float *longitude)
{
    int items_read = 0;

    // time
    items_read = scanf("%d", time);
    if (items_read <= 0)
        return -1;

    // lat
    items_read = scanf("%f", latitude);
    if (items_read <= 0)
        return -1;

    // lat
    items_read = scanf("%f", longitude);
    if (items_read <= 0)
        return -1;

    
    return 0;
}
