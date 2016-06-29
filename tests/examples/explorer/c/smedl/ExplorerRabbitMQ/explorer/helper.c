#include <stdlib.h>
#include "explorer_mon.h"


//input size should be known before hand
const int ROWNUM = 30;
const int COLUMNNUM = 60;


int contains_object(void* map) {
    int *p=(int*)map;
    for(int i = 0; i < 3; i++) {
        for(int j = 0; j < 3; j++) {
            if(p[i*3+j] > 0) {
                return 1;
            }
        }
    }
    return 0;
}

int check_retrieved(void* map,int x,int y){
  int *p=(int*)map;
  if(*(p+y*COLUMNNUM+x) > 0){
     return 1;
  }
  return 0;
}


