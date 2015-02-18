#include <stdio.h>
#include <pthread.h>
#include <time.h>

struct MeanderData {
  int id, thresh_up, thresh_down, speed;
};

enum Dir { UP, DOWN };

void* meander( void* thread_data ) {
  struct MeanderData* md = (struct MeanderData*) thread_data;
  int d = UP;
  int pos = md->thresh_down;
  struct timespec t1, t2;

  while (1) {
    if (d==DOWN) {
       pos = pos - 1;
       if (pos <= md->thresh_down)
          d = UP;
    } else if (d==UP) {
       pos = pos + 1;
       if (pos >= md->thresh_up)
          d = DOWN;
    }
    printf("%d: %d\n", md->id, pos);
    t1.tv_sec = 0;
    t1.tv_nsec = md->speed * 1000000;
    nanosleep(&t1,&t2);
  }
}

int main (void) {

  pthread_t thread1, thread2;

  struct MeanderData md1, md2;

  md1.id = 1;
  md1.thresh_down = 0;
  md1.thresh_up = 20;
  md1.speed = 10;
  md2.id = 2;
  md2.thresh_down = 5;
  md2.thresh_up = 15;
  md2.speed = 15;

  pthread_create( &thread1, NULL, meander, &md1 );
  pthread_create( &thread2, NULL, meander, &md2 );

  pthread_join( thread1, NULL );
  pthread_join( thread2, NULL );
}
