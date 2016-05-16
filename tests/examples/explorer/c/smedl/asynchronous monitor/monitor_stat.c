#include <stdio.h>
#include <stdlib.h>
#include "explorer_stat_mon.h"

int main()
{
    int robotNum = 10;
    int target = 5;
   ExplorerstatData *statData = (ExplorerstatData*)malloc(sizeof(ExplorerstatData));
    int * i = 0;
    statData -> id = &i;
    statData -> sum = 0;
    statData -> count = 0;
    statData -> targetNum = robotNum * target;
   init_explorerstat_monitor_maps();
   ExplorerstatMonitor* mon = init_explorerstat_monitor(statData);
   start_monitor(mon);
    while(1){}

   //TODO: subscribe to broker, receive retrieved event and publish output event
   free(statData);
   free_monitor(mon);
   return 0;
}
