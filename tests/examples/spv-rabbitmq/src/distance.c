#include <math.h>
#include <stdio.h>

#include "parser.h"

#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <assert.h>

 void send_message(char* message, char* routing_key);

float total_distance()
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

    while (1) {
        int result = parse_record(&time, &latitude, &longitude);
        if (result == -1)
            break;
        
        char message[256];
        sprintf(message, "spv_parse_record %d %f %f %d", time,latitude,longitude,result);
        char routing_key[256] = "spv-spv_parse_record.0.spv_parse_record";
        send_message(message,routing_key);
        
        if (is_first_pt) {
            is_first_pt = 0;
        } else {
            // manhattan distance
            total_dist += fabs(last_lat - latitude)
                          + fabs(last_long - longitude);
        }
        last_lat = latitude;
        last_long = longitude;
    }

    return total_dist;
}
