#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

#ifndef DETECTIONDB_H
#define DETECTIONDB_H



#ifdef _c_plusplus
extern "C"
{
#endif


void addDetection(double ts, double lat, double lon, double alt, double snr); 
void removeDetection(double ts, double lat, double lon, double alt); 
void clearDetections();
int getNumUnused(int dummy);

  void addReport(double ts, int id, double lat, double lon, double alt, double vlat, double vlon, double valt, void *monp);

void reportTrackMetrics(double lastTime, double interval, void * monp);

  
void initUdf(void *monp);
void startUdfMonitor(double ts);
void addToSubInterval(double ts, int val);
void addTrackReport(double ts, int trackId, void *monp);
int udfComputeIntervalMetric(void *monp);
void computeMeanSnr(double start, double end, void *monp);

#ifdef _c_plusplus
}
#endif

#endif // DETECTIONDB_H
