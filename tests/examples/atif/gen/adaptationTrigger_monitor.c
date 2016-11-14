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
#include "adaptationTrigger_mon.h"

int main()
{
    AdaptationtriggerData *data = (AdaptationtriggerData*)malloc(sizeof(AdaptationtriggerData));

    data->id = (int*)malloc(sizeof(int));
    (data->id) = 0;
    data-> Tw =  0;
    data-> Tat = 0;
    data-> Tib = 0;

    data-> TwID  =  "0";
    data-> TatID = "1";
    data-> TibID = "2";
    data-> enabled = 1;

    init_adaptationtrigger_monitor_maps();

    AdaptationtriggerMonitor *mon = init_adaptationtrigger_monitor(data);

    start_monitor(mon);

    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}
