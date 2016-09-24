#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include "SimpleParserMon_mon.h"

int main(int argc, char * argv[])
{
    int time;
    float latitude;
    float longitude;
    float last_lat;
    float last_long;
    // Total 'distance' traveled. Use manhattan distance for simplicity.
    // Note that this won't correspond well to actual distance, since
    // we are just counting change in lat/lon rather than meters.
    float total_dist = 0.0;
    _Bool is_first_pt = 1;
    int monid = 0;

    init_simpleparsermon_monitor_maps();
    SimpleparsermonData* data = (SimpleparsermonData*)malloc(sizeof(SimpleparsermonData));
    data -> id = &monid;
    data -> currentTime = 0;
    SimpleparsermonMonitor* monitor = init_simpleparsermon_monitor(data);

    while (1) {
        int items_read = 0;
        // time
        items_read = scanf("%d", &time);
        if (items_read <= 0)
            break;
	    simpleparsermon_getTime_probe(time);

        // lat
        items_read = scanf("%f", &latitude);
        if (items_read <= 0)
            break;
	    simpleparsermon_getLat_probe(latitude);

        // lat
        items_read = scanf("%f", &longitude);
        if (items_read <= 0)
            break;
	    simpleparsermon_getLon_probe(longitude);

        if (is_first_pt) {
            is_first_pt = 0;
        } else {
            // manhattan distance
            total_dist += fabs(last_lat - latitude)
                        + fabs(last_long - longitude);
	        simpleparsermon_getDist_probe(total_dist);
        }
        last_lat = latitude;
        last_long = longitude;
    }

    printf("Total Manhattan Distance: %f\n", total_dist);
    return 0;
}
