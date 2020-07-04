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
#include "stringRate_mon.h"

int main(int argc, char *argv[])
{
    RatecomputationData *data = (RatecomputationData*)malloc(sizeof(RatecomputationData));
    int localId = 0;
    if (argc >= 2)
      {
	localId = atoi(argv[1]);
      }
    
    data->id = (int*)malloc(sizeof(int));
    (data->id) = localId;
    data->lastTime = 0;
    data->curTime = 0;
    data->sum = 0;
    //data-> warnLevel = 2;
    //data-> numWarnings = 0;
    data-> name = "0";
    printf("init instrumentation monitor %d\n", localId);

    init_ratecomputation_monitor_maps();
    RatecomputationMonitor* mon = init_ratecomputation_monitor(data);

    printf("start monitor\n");
    start_monitor(mon);

    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}
