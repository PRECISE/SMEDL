#include <stdlib.h>

typedef enum { MAIN, EXPLORE, RETRIEVE } scenario;
typedef enum { EXPLORE_MAIN, RETRIEVE_MAIN } main_state;
typedef enum { EXPLORE_EXPLORE, RETRIEVE_EXPLORE, SCAN_EXPLORE, GEN0_EXPLORE } explore_state;
typedef enum { RETRIEVE_RETRIEVE, EXPLORE_RETRIEVE } retrieve_state;
typedef enum { DEFAULT } error_type;

typedef struct _Explorer{
  int interest_threshold;
  int y;
  int x;
  int heading;
  int state[3]; // = { EXPLORE_MAIN, EXPLORE_EXPLORE, RETRIEVE_RETRIEVE };
} _Explorer;

void catch(_Explorer *, int, int, error_type);

void retrieved(_Explorer* monitor) {
  switch (monitor->state[MAIN]) {
    case RETRIEVE_MAIN:
      monitor->state[MAIN] = EXPLORE_MAIN;
      break;
    default:
      catch(monitor, MAIN, monitor->state[MAIN], 0);
      break;
  }
  switch (monitor->state[EXPLORE]) {
    default:
      catch(monitor, EXPLORE, monitor->state[EXPLORE], 0);
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    case RETRIEVE_RETRIEVE:
      monitor->state[RETRIEVE] = EXPLORE_RETRIEVE;
      break;
    default:
      catch(monitor, RETRIEVE, monitor->state[RETRIEVE], 0);
      break;
  }
}

void drive(_Explorer* monitor, int x, int y, int heading) {
  switch (monitor->state[MAIN]) {
    default:
      catch(monitor, MAIN, monitor->state[MAIN], 0);
      break;
  }
  switch (monitor->state[EXPLORE]) {
    default:
      catch(monitor, EXPLORE, monitor->state[EXPLORE], 0);
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    case RETRIEVE_RETRIEVE:
      if(x != monitor->x && y != monitor->y) {
        monitor->state[RETRIEVE] = RETRIEVE_RETRIEVE;
      }
      break;
    default:
      catch(monitor, RETRIEVE, monitor->state[RETRIEVE], 0);
      break;
  }
}

void turn(_Explorer* monitor) {
  switch (monitor->state[MAIN]) {
    default:
      catch(monitor, MAIN, monitor->state[MAIN], 0);
      break;
  }
  switch (monitor->state[EXPLORE]) {
    case SCAN_EXPLORE:
      if(turn() != heading) {
        monitor->state[EXPLORE] = GEN0_EXPLORE;
      }
      break;
    default:
      catch(monitor, EXPLORE, monitor->state[EXPLORE], 0);
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    default:
      catch(monitor, RETRIEVE, monitor->state[RETRIEVE], 0);
      break;
  }
}

void found(_Explorer* monitor) {
  switch (monitor->state[MAIN]) {
    case EXPLORE_MAIN:
      monitor->state[MAIN] = RETRIEVE_MAIN;
      break;
    default:
      catch(monitor, MAIN, monitor->state[MAIN], 0);
      break;
  }
  switch (monitor->state[EXPLORE]) {
    default:
      catch(monitor, EXPLORE, monitor->state[EXPLORE], 0);
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    default:
      catch(monitor, RETRIEVE, monitor->state[RETRIEVE], 0);
      break;
  }
}

void view(_Explorer* monitor, int x, int y) {
  switch (monitor->state[MAIN]) {
    default:
      catch(monitor, MAIN, monitor->state[MAIN], 0);
      break;
  }
  switch (monitor->state[EXPLORE]) {
    case EXPLORE_EXPLORE:
      if(contains_object(view(x, y))) {
        monitor->state[EXPLORE] = RETRIEVE_EXPLORE;
      }
      break;
    default:
      catch(monitor, EXPLORE, monitor->state[EXPLORE], 0);
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    default:
      catch(monitor, RETRIEVE, monitor->state[RETRIEVE], 0);
      break;
  }
}

void catch(_Explorer *mon, int scen, int next_state, error_type error) {
  int recovered = 0;
  switch(error) {
    case DEFAULT:
      //Call to specified function in user's recovery .h file
      break;
    default:
      recovered = 1;
      break;
  }
  if(recovered) {
    mon->state[scen] = next_state; //Default action
  } else {
    exit(EXIT_FAILURE);
  }
  return;
}