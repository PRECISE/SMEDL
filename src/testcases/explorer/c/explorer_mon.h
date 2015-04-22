#ifndef EXPLORER_MON_H
#define EXPLORER_MON_H

struct _Explorer;

// checker initialization

struct _Explorer* init_Explorer(int interest_threshold, int y, int x, int heading);

// checker event interface

void retrieved(struct _Explorer* monitor);
void drive(struct _Explorer* monitor, int x, int y, int heading);
void turn(struct _Explorer* monitor, int facing);

// checker lookup interface

void addChecker( struct _Explorer* );
struct _Explorer* getChecker( int );

// dummy checker storage

void initCheckerStorage();

#endif
