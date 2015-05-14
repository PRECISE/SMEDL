#include "actions.h"

#ifndef EXPLORER_MON_H
#define EXPLORER_MON_H

typedef struct ExplorerData{
  int y;
  int x;
  int heading;
} ExplorerData;

typedef struct _Explorer{
  struct ExplorerData *id;
  int interest_threshold;
  int y;
  int x;
  int heading;
  void *explorer_view;
  int state[2]; // = { EXPLORE_MAIN, MOVE_EXPLORE };
  const char **state_names[2];
  action *action_queue;
} _Explorer;

// checker initialization

struct _Explorer* init_Explorer(struct ExplorerData*);

// checker event interface

void retrieved(struct _Explorer* monitor);
void drive(struct _Explorer* monitor, int x, int y, int heading);
void turn(struct _Explorer* monitor, int facing);
void scan_view(_Explorer*, int, int, int, const void*);

// checker lookup interface

void add_checker( struct _Explorer* );
struct _Explorer* get_checker(const struct ExplorerData*);

// dummy checker storage

void init_checker_storage();

#endif
