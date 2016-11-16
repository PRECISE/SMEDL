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
#include "string_mon.h"

int main(int argc, char *argv[])
{
    StringtestData *data = (StringtestData*)malloc(sizeof(StringtestData));
    int localId = 0;
    if (argc >= 2)
    {
        localId = atoi(argv[1]);
    }
    
    data->id = (int*)malloc(sizeof(int*));
    (data->id) = &localId;


    init_stringtest_monitor_maps();
    StringtestMonitor* mon = init_stringtest_monitor(data);

    printf("start monitor\n");
    start_monitor(mon);

    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}
