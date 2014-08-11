#include <stdio.h>

#include "meander.h"
#include "safemon.h"

enum { SAFEMON, SWITCH } stateset;

typedef struct _SafeMon {
  const struct MeanderData* id;
  int upbound, lobound;
  int currentState;
} _SafeMon;

_SafeMon* initSafeMon( const struct MeanderData* t ) {
  _SafeMon* newchecker = (_SafeMon*) malloc( sizeof(_SafeMon) );
  newchecker->id = t;
  newchecker->lobound = t->thresh_down;
  newchecker->upbound = t->thresh_up;
  newchecker->currentState = SAFEMON;
}

void updatePos( _SafeMon* c, int x ) { 
  switch (c->currentState) {
  case SAFEMON:
      if (c->upbound == x || c->lobound == x) {
        c->currentState = SWITCH; 
        printf( "bound reached in %d\n", c->id->id );
      }
      break;
  case SWITCH:
      // raise an error, need to figure out the error API;
      printf("illegal transition from state %d on event updatePos\n", 
             c->currentState);
  }
}

void changeDir( _SafeMon* c ) { 
  switch (c->currentState) {
  case SWITCH:
      c->currentState = SAFEMON; 
      break;
  case SAFEMON:
      c->currentState = SAFEMON;
  }
  printf( "switching in %d\n", c->id->id );
}

// this is intentionally naive, for illustrational purposes only

typedef struct CheckerRecord {
  _SafeMon* checker;
  struct CheckerRecord* next;
} CheckerRecord;

CheckerRecord* checkStore;

void initCheckerStorage() {
  checkStore = NULL;
}

void addChecker( const struct MeanderData* key, _SafeMon* c) {
  CheckerRecord* tmp = checkStore;
  checkStore = (CheckerRecord*)malloc(sizeof(CheckerRecord));
  checkStore->checker = c;
  checkStore->next = tmp;
}

_SafeMon* getChecker( const struct MeanderData* key ) {
  CheckerRecord* iter = checkStore;
  while (iter != NULL) {
    if (iter->checker->id == key) 
       break;
    iter = iter->next;
  }
  return iter->checker;
}

