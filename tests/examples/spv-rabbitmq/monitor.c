#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "spv_mon.h"

int spv_mon_id=0;
int main()
{
    SpvData *data = (SpvData*)malloc(sizeof(SpvData));
    init_spv_monitor_maps();
    data->id = &spv_mon_id;
    data->last_time = 0;
    SpvMonitor* mon = init_spv_monitor(data);
    printf("after init\n");
    int time;
    float lat;
    float lon;
    float distance;
    int ret;

    start_monitor(mon);
    
    // In the header but not implemented?
    // free_spv_monitor();
    // free_spv_monitor_maps();
    free_monitor(mon);
    free(data);

    return 0;
}


