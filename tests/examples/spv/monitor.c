#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <libconfig.h>
#include "spv_mon.h"

int main()
{
    SpvData *data = (SpvData*)malloc(sizeof(SpvData));

    int id = 0;
    data->id = &id;
    data->last_time = 0;
    
    init_spv_monitor_maps();
    SpvMonitor* mon = init_spv_monitor(data);

    start_monitor(mon);

    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}
