#include <stdio.h>
#include <string.h>
#include <stdlib.h>

// monitoring code
#include "overflow_mon.h"
// monitoring code

int main( int argc, char* argv[] )
{
  int source[10000];
  int* buffer;
  // monitoring code
  OvfmonMonitor* buffer_monitor = (OvfmonMonitor*)malloc(sizeof(OvfmonMonitor));
  buffer_monitor->size = 0;
  // monitoring code
  int i;

  // monitoring code
  ovfmon_reinit( buffer_monitor, 1000 );
  // monitoring code
  buffer = (int*)malloc( 10000*sizeof(int) );
  if (!buffer) {
     printf("buffer allocation failed");
     return -1;
  }
  // monitoring code
  ovfmon_write( buffer_monitor, 1000 );
  // monitoring code
  memcpy( buffer, source, 10000*sizeof(int) );
  
  printf("success\n");

  free(buffer);

  // monitoring code
  ovfmon_reinit( buffer_monitor, 50 );
  // monitoring code
  buffer = malloc( 50*sizeof(int) );
  if (!buffer) {
     printf("buffer allocation failed");
     return -1;
  }
  // monitoring code
  ovfmon_write( buffer_monitor, 1000 );
  // monitoring code
  memcpy( buffer, source, 10000*sizeof(int) );
  printf("failure?\n");
  
  return 0;
}
