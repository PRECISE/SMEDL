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
#include "stringThresh_mon.h"




int main(int argc, char *argv[])
{
    int localId = 0;
    if (argc >= 2)
      {
	localId = atoi(argv[1]);
      }
    
    ThresholdcrossdetectionData *data = (ThresholdcrossdetectionData*)malloc(sizeof(ThresholdcrossdetectionData));

    data->id = (int*)malloc(sizeof(int));
    (data->id) = localId;
    data-> xingTime = 0;
    data-> threshold = 1;
    data-> holdTime = 0;
    data-> trigger = 0;
    //   data-> valName = "Hello";

    printf("init thresh monitor %d\n", localId);

    init_thresholdcrossdetection_monitor_maps();
    ThresholdcrossdetectionMonitor* mon = init_thresholdcrossdetection_monitor(data);
    printf("starting threshold monitor\n");

    start_monitor(mon);

    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}
