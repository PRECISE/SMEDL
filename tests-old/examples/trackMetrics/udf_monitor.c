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
#include "udf_mon.h"
#include <ctype.h>

#include "detectionDb.h"

int main(int argc, char *argv[])
{
    UdfData *data = (UdfData*)malloc(sizeof(UdfData));
    int localId = 0;
    if (argc >= 2)
      {
	localId = atoi(argv[1]);
      }
    
    data-> id = localId;
    data->  interval = 30000.0;
    data->  slidingWindowInterval = 5000;
    data->  delay = 10000;
    data->  uddb = 0;
    data->  lastTime = 0.0;
    data->  timerEnabled = 0;


    data->  timePerTrack = 0;
    data->  distancePerTrack = 0;
    data->  intervalDistThreshold = 50;  // no idea what this should be - differs between mounts and dismounts, etc
    data->  intervalTimeThreshold = 15;  // default to 50% of interval

    // udf intervals to match observed time intervals
    // since interval timing is tricky
    data->udfIntervalLength = 30;
    data->udfNumSubIntervals = 6;
    data->trackerNScan = 4;
    data->  numUnassociated = 0;
    data->  totalDetections = 0;
    data->percentUnassociatedDetections = 0;
    data->udfStarted = 0;
    data->  lastTimeUdf = 0.0;
    data-> subIntervalLength = 0;
    data-> intervalMeanSnr = 0;
    
    data->accTs = 0;
    data->accTrackId = 0;
    data->accAccel = 0;
    data->accAz = 0;
    data->accEl = 0;

    data->unusedThreshold = 40.0;
      
    printf("init UDF monitor %d %s\n", localId, "");

    init_udf_monitor_maps();
    UdfMonitor* mon = init_udf_monitor(data);
    
    char *testFile = NULL;
    if (argc >= 3)
      {
	testFile = argv[2];
	extern void unittest(char *filename, UdfMonitor *monitor);
	unittest(testFile, mon);
	exit(0);
      }


    printf("start monitor\n");
    start_monitor(mon);

    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}




