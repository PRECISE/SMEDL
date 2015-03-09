#include <stdlib.h>

enum { MAIN, EXPLORE, RETRIEVE } scenarios;
enum { EXPLORE_MAIN, RETRIEVE_MAIN } main_states;
enum { EXPLORE_EXPLORE, RETRIEVE_EXPLORE, SCAN_EXPLORE, GEN0_EXPLORE } explore_states;
enum { RETRIEVE_RETRIEVE, EXPLORE_RETRIEVE } retrieve_states;
enum { DEFAULT } error_types;

typedef struct _Explorer{
  int interest_threshold;
  int y;
  int x;
  int heading;
  int state[3] = { EXPLORE_MAIN, EXPLORE_EXPLORE, RETRIEVE_RETRIEVE };
} _Explorer;

void retrieved(_Explorer* monitor) {
  switch (monitor->state[MAIN]) {
    case RETRIEVE:
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
    case RETRIEVE:
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
    case RETRIEVE:
      if(x != object.x && y != object.y) {
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
    case SCAN:
      if(turn(None) != heading) {
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
    case EXPLORE:
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
    case EXPLORE:
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

void catch(_Explorer *mon, scenario scen, int next_state, error_types error) {
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
    mon->current_states[scen] = next_state; //Default action
  } else {
    exit(EXIT_FAILURE);
  }
  return;
}