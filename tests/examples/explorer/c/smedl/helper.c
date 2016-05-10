#include <stdlib.h>
#include "explorer_mon.h"

/*int *get_coordinates(ExplorerMonitor *monitor) {
    int *coords = (int*)malloc(sizeof(int) * 2);
    if(monitor->heading == 0) { //up
        coords[0] = monitor->y - 2;
        coords[1] = monitor->x - 1;
    } else if(monitor->heading == 1) { //left
        coords[0] = monitor->y - 1;
        coords[1] = monitor->x - 3;
    } else if(monitor->heading == 2) { //down
        coords[0] = monitor->y + 1;
        coords[1] = monitor->x - 1;
    } else if(monitor->heading == 3) { //right
        coords[0] = monitor->y - 1;
        coords[1] = monitor->x + 1;
    }
    return coords;
}*/

/*void set_view(ExplorerMonitor *monitor, const void *map) {
    monitor->explorer_view = (int***)malloc(sizeof(int**)*3);
    for(int i = 0; i < 3; i++) {
        ((int***)monitor->explorer_view)[i] = (int**)malloc(sizeof(int*)*3);
    }
    int *coords = get_coordinates(monitor);
    for(int i = 0; i < 3; i++) {
        for(int j = 0; j < 3; j++) {
            ((int***)monitor->explorer_view)[i][j] = &((int**)map)[coords[0] + i][coords[1] + j];
        }
    }
}*/

int contains_object(void * pointer) {
    for(int i = 0; i < 3; i++) {
        for(int j = 0; j < 3; j++) {
            if(((int**)pointer)[i][j]  > 0) {
                return 1;
            }
        }
    }
    return 0;
}

/*void free_view(ExplorerMonitor *monitor) {
    for(int i = 0; i < 3; i++) {
        free(((int***)monitor->explorer_view)[i]);
    }
    free(monitor->explorer_view);
}*/