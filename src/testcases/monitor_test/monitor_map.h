// the initial capacity (number of buckets)
#define EXPLORER_MONITOR_MAP_SIZE 100
#define EXPLORER_IDENTITIES 3

typedef enum { INT, POINTER, THREAD } identity_type;

typedef struct MonitorIdentity {
  identity_type type;
  void *value;
} MonitorIdentity;

MonitorIdentity* init_MonitorIdentity(identity_type, void*);
int compare_MonitorIdentity(void*, MonitorIdentity*);
int hash_MonitorIdentity(identity_type, void*);

typedef struct _Explorer{
  MonitorIdentity *identities[3];
  int y;
  int x;
} _Explorer;

typedef struct ExplorerMonitorRecord {
  _Explorer *monitor;
  struct ExplorerMonitorRecord *next; // next node in the list
} ExplorerMonitorRecord;

typedef struct ExplorerMonitorMap {
  ExplorerMonitorRecord *list[EXPLORER_MONITOR_MAP_SIZE]; // "buckets" of linked lists
} ExplorerMonitorMap;

ExplorerMonitorMap* explorer_monitor_maps[EXPLORER_IDENTITIES]; //a map for each identity

/* Function prototypes */
_Explorer* init_Explorer(int, void*, pthread_t*, int, int);
void init_explorer_maps();
int add_explorer_to_map(_Explorer*, int);
int put_explorer_monitor(_Explorer*); //puts into all maps
ExplorerMonitorRecord* get_explorer_by_identity(int, int, void*);
ExplorerMonitorRecord* filter_explorer_by_identity(ExplorerMonitorRecord*, int, void*);
// void init_explorer_monitor_store();
// void free_explorer_monitor_store();
