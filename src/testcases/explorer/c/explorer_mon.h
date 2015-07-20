#include "actions.h"

#ifndef EXPLORER_MON_H
#define EXPLORER_MON_H

// Checker initialization

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
  action *action_queue;
} _Explorer;

struct _Explorer* init_Explorer(ExplorerData*);
void free_Explorer(_Explorer*);

// Checker storage and lookup

typedef struct CheckerRecord {
  _Explorer* checker;
  struct CheckerRecord* next;
} CheckerRecord;

CheckerRecord* checkStore;

void init_checker_storage();
void free_checker_storage();
void add_checker(_Explorer*);
_Explorer* get_checker(const ExplorerData*);

// Checker event interface

void drive(_Explorer*, int, int, int);
void raise_drive(_Explorer*, int, int, int);

void turn(_Explorer*, int);
void raise_turn(_Explorer*, int);

void scan_view(_Explorer*, int, int, int, const void*);
void raise_scan_view(_Explorer*, int, int, int, const void*);

void found(_Explorer*); 
void raise_found(_Explorer*);

void retrieved(_Explorer*);
void raise_retrieved(_Explorer*);

// Checker action and error raises

void call_next_action(_Explorer*);
void exec_actions(_Explorer*);
void raise_error(char*, const char*, char*, char*);

#endif
