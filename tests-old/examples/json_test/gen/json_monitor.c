typedef char *string;

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <libconfig.h>
#include "json_mon.h"

int main(int argc, char *argv[])
{
    JsontestData *data = (JsontestData*)malloc(sizeof(JsontestData));
    int localId = 0;
    if (argc >= 2)
    {
        localId = atoi(argv[1]);
    }
    
    data->id = (int*)malloc(sizeof(int*));
    (data->id) = &localId;


    init_jsontest_monitor_maps();
    JsontestMonitor* mon = init_jsontest_monitor(data);

    printf("start monitor\n");
    start_monitor(mon);

    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}
