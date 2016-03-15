#include <stdio.h>
#include <stdlib.h>
#include "spv_mon.h"

int main()
{
    SpvData *data = (SpvData*)malloc(sizeof(SpvData));
    init_spv_monitor_maps();
    SpvMonitor* mon = init_spv_monitor(data);

    int time;
    float lat;
    float lon;
    int ret;

    int i = 0;
    for (i = 0; i < 10; i++)  {
        // call parse_record time lat lon
        if (0 > scanf("%*[^,],%*[^,],%*d,%*f,%*f")) break;

        // return parse_record time lat lon return
        if (0 > scanf("%*[^,],%*[^,],%d,%f,%f,%d", &time, &lat, &lon, &ret)) break;

        spv_parse_record(mon, time, lat, lon, ret);
    }

    // In the header but not implemented?
    // free_spv_monitor_maps();
    free(data);
    free_monitor(mon);

    return 0;
}
