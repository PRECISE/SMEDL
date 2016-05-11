#include <stdio.h>
#include <stdlib.h>
#include "explorer_stat_mon.h"

int main()
{
   Explorer_statData *statData = (Explorer_statData 
*)malloc(sizeof(Explorer_statData));
   init_explorer_stat_monitor_maps();
   Explorer_statMonitor* mon = init_explorer_stat_monitor(statData);

   //TODO: subscribe to broker, receive retrieved event and publish output event
   free(statData);
   free_monitor(mon);
   return 0;
}
