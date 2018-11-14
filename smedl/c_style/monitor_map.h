#ifndef MONITOR_MAP_H
#define MONITOR_MAP_H

typedef enum { INT, POINTER, THREAD, OPAQUE, STRING } identity_type;

typedef struct MonitorIdentity {
  identity_type type;
  void *value;
} MonitorIdentity;

MonitorIdentity* init_monitor_identity(identity_type, void*);
int compare_monitor_identity(void*, MonitorIdentity*);
int compare_identity(MonitorIdentity*, MonitorIdentity*)
int compare_identity_2(void*, MonitorIdentity*)
int hash_monitor_identity(identity_type, void*, int);
char* monitor_identity_str(MonitorIdentity*);

#endif
