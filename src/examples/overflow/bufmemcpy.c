#include <stdio.h>
#include <string.h>
#include <stdlib.h>

int main( int argc, char* argv[] )
{
  int source[10000];
  int* buffer;
  int i;

  buffer = (int*)malloc( 10000*sizeof(int) );
  if (!buffer) {
     printf("buffer allocation failed");
     return -1;
  }
  memcpy( buffer, source, 10000*sizeof(int) );
  
  printf("success\n");

  free(buffer);

  buffer = malloc( 50*sizeof(int) );
  if (!buffer) {
     printf("buffer allocation failed");
     return -1;
  }
  memcpy( buffer, source, 10000*sizeof(int) );
  printf("failure?\n");
  
  return 0;
}
