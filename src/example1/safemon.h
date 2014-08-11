struct _SafeMon;

// checker initialization

struct _SafeMon* initSafeMon( const struct MeanderData* t );

// checker event interface

void update( struct _SafeMon* c, int x );
void changeDir( struct _SafeMon* c );

// checker lookup interface

void addChecker( const struct MeanderData*, struct _SafeMon* );
struct _SafeMon* getChecker( const struct MeanderData* );

// dummy checker storage

void initCheckerStorage();
