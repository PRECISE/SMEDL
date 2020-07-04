/*
Header

Copyright BAE Systems 2017 
*/


#include <vector>
#include <iostream>
#include <fstream>

#include <stdlib.h>
#include <math.h>
static const double earthRadius = 6371000;

extern "C"
{
#include "detectionDb.h"
#include "udf_mon.h"

void unittest(char *filename, UdfMonitor *monitor);
}

using namespace std;


// local functions
double calcDistance(double lat1, double lon1, double lat2, double lon2);
double calcDistance2(double lat1, double lon1, double lat2, double lon2);
class TrackReport;
void calcAccel(TrackReport *from, TrackReport *to, double *accel, double *az, double *el);




class Detection
{
public:
  Detection(double ts, double lat, double lon, double alt, double snr) :
    ts(ts),
    lat(lat),
    lon(lon),
    alt(alt),
    snr(snr)
  {}
  double ts;
  double lat;
  double lon;
  double alt;
  double snr;
};



enum TrackReportType
  {
    DETECTED,
    COAST,
    DROP,
    INITIAL
  };



class TrackReport
{
public:
  double time;
  double lat;
  double lon;
  double alt;
  double vlat;
  double vlon;
  double valt;
  TrackReportType type;
  TrackReport(double ts, double lat, double lon, double alt, double vlat, double vlon, double valt) :
    time(ts), lat(lat), lon(lon), alt(alt), vlat(vlat), vlon(vlon), valt(valt), type(DETECTED)
  {}
};




class Track
{
public:
  int trackId;
  double startTime;
  double lastUpdate;
  bool dropped;
  double timeInTrack;
  double distanceInTrack;
  TrackReport *lastReport;
  std::vector<TrackReport *> reports;

  double getTrackedTimeInInterval(double start, double end)
  {
    double retval = 0;
    double trackStart = 0;
    double trackEnd = 0;
    // TrackReport *prior = NULL;
    int f = (int) findIndexOfFirstInInterval(start, end);
    int l = (int) findIndexOfLastInInterval(start, end);
    if (f != -1 && l != -1)
      {
	if (f == 0)
	  {
	    trackStart = reports[f]->time;
	  }
	else
	  {
	    trackStart = start;
	  }
	if (l == (int) (reports.size() - 1))
	  {
	    trackEnd = reports[l]->time;
	  }
	else
	  {
	    trackEnd = end;
	  }
	retval = trackEnd - trackStart;
      }
    return retval;
  }

  double getTrackedDistanceInInterval(double start, double end)
  {
    double retval = 0;
    // TrackReport *prior = NULL;
    int f = (int) findIndexOfFirstInInterval(start, end);
    int l = (int) findIndexOfLastInInterval(start, end);
    if (f != -1 && l != -1)
      {
	if (f == 0)
	  {
	  }
	else
	  {
	    double distToPrevPoint= calcDistance(reports[f-1]->lat, reports[f-1]->lon, reports[f]->lat, reports[f]->lon);
	    double iterpolation = (reports[f]->time - start) / (reports[f]->time - reports[f-1]->time);
	    double distFromIntervalStartToFirstPoint = distToPrevPoint * iterpolation;
	    retval += distFromIntervalStartToFirstPoint;
	  }

	for (int i = f + 1; i <= l; i++)
	  {
	    retval += calcDistance(reports[i-1]->lat, reports[i-1]->lon, reports[i]->lat, reports[i]->lon);
	  }
	
	if (l == (int) (reports.size() - 1))
	  {
	  }
	else
	  {
	    double distToNextPoint= calcDistance(reports[l]->lat, reports[l]->lon, reports[l+1]->lat, reports[l+1]->lon);
	    double iterpolation = (end - reports[l]->time) / (reports[l+1]->time - reports[l]->time);
	    double distFromIntervalEndToLastPoint = distToNextPoint * iterpolation;
	    retval += distFromIntervalEndToLastPoint;
	  }
      }
    return retval;
  }

  bool hasReportsInInterval(double start, double end)
  {
    int i = findIndexOfFirstInInterval(start, end);
    return ( i != -1 );
  }

  int findIndexOfFirstInInterval(double start, double end)
  {
    int retval = -1;
    TrackReport *r = NULL;
    for(unsigned int i = 0; i < reports.size() && retval == -1; i++)
      {
	r = reports[i];
	if (r->time >= start && r->time < end)
	  {
	    retval = i;
	  }
      }
    return retval;
  }
  

  int findIndexOfLastInInterval(double start, double end)
  {
    int retval = -1;
    TrackReport *r = NULL;
    for(int i = (int) reports.size() - 1; i >= 0 && retval == -1; i--)
      {
	r = reports[i];
	if (r->time >= start && r->time < end)
	  {
	    retval = i;
	  }
      }
    return retval;
  }
  

  void addReport(TrackReport *update, void *monp)
  {
    TrackReport *prev = NULL;

    if (!reports.empty())
      {
	prev = reports.back();
      }

    reports.push_back(update);
    double accel = 0.0;
    double az = 0.0;
    double el = 0.0;
    if (startTime == -1.0)
      {
	startTime = update->time;
	lastReport = update;
      }
    else
      {
	distanceInTrack += calcDistance(lastReport->lat, lastReport->lon, update->lat, update->lon);
	timeInTrack += update->time - lastReport->time;
	lastReport = update;
	lastUpdate = update->time;

	calcAccel(prev, update, &accel, &az, &el);
      }
    cout << "TrackID " << trackId
	 << " time " << update->time
	 << " distanceInTrack " << distanceInTrack
	 << " timeInTrack " << timeInTrack
	 << "\n Acceleration of trackID " << trackId << " is " << accel << " direction " << az << " deg (az) " << el << " deg (el)" 
	 << endl;

    UdfMonitor *monitor = (UdfMonitor *) monp;
    if (monitor != NULL && startTime > 0.0)
      {
    	monitor->accTs = update->time;
	monitor->accTrackId = trackId;
	monitor->accAccel = accel;
	monitor->accAz = az;
	monitor->accEl = el;
      }
    else
      {
    	monitor->accTs = -1;
	monitor->accTrackId = -1;
	monitor->accAccel = -1;
	monitor->accAz = -1;
	monitor->accEl = -1;	
      }
  };
  Track(int id) :trackId(id)
  {
    startTime = -1.0;
    lastUpdate = 0.0;
    dropped = false;
    timeInTrack = 0.0;
    distanceInTrack = 0.0;
    lastReport = NULL;
  };
  ~Track()
  {
    // ???? clean up track reports
  }

};   // end class Track
  

class TrackDB
{
public:
  std::vector<Track> tracks;
  // number of detections that must be associated before a track is declared
  int pointsToTrackInitiation;
  bool trackExists(int id) { return (NULL != this->getTrack(id)); };
  Track *getTrack(int id)
  {
    Track *retval = NULL;
    for(std::vector<Track>::iterator it=tracks.begin() ; it < tracks.end(); it++ )
      {
	if ((*it).trackId == id)
	  {
	    retval = &(*it);
	    break;
	  }
      }
    return retval;
  };
  Track *getOrCreateTrack(int id)
  {
    Track *retval = getTrack(id);
    if (retval == NULL)
      {
	retval = new Track(id);
	tracks.push_back(*retval);
	retval = getTrack(id);
      }
    return retval;
  };
  void addReport(double ts, int id, double lat, double lon, double alt, double vlat, double vlon, double valt, void *monp)
  {
    Track *track = getOrCreateTrack(id);
    TrackReport *rpt = new TrackReport(ts, lat, lon, alt, vlat, vlon, valt);
    track->addReport(rpt, monp);
  };
  int getTotalTracks() { return tracks.size(); };
  int getTracksInInterval(double start, double end)
  {
    int retval = 0;
    for(std::vector<Track>::iterator it=tracks.begin() ; it < tracks.end(); it++ )
      {
	if ( (*it).hasReportsInInterval(start, end) )
	  // if ( ((*it).lastUpdate >= start) && (((*it).lastUpdate <= end) ))
	  {
	    retval++;
	  }
      }
    return retval;
  };
  double getTotalTrackDistance()
  {
    double retval = 0.0;
    for(std::vector<Track>::iterator it=tracks.begin() ; it < tracks.end(); it++ )
      {
	retval += (*it).distanceInTrack;
      }
    return retval;
  };
  double getTotalTrackDistanceInterval(double start, double end)
  {
    int retval = 0;
    for(std::vector<Track>::iterator it=tracks.begin() ; it < tracks.end(); it++ )
      {
	retval += (*it).getTrackedDistanceInInterval(start, end);
      }
    return retval;
  };
  double getTotalTrackTime()
  {
    double retval = 0.0;
    for(std::vector<Track>::iterator it=tracks.begin() ; it < tracks.end(); it++ )
      {
	retval += (*it).timeInTrack;
      }
    return retval;
  };
  double getTotalTrackTimeInterval(double start, double end)
  {
    double retval = 0;
    for(std::vector<Track>::iterator it=tracks.begin() ; it < tracks.end(); it++ )
      {
	retval += (*it).getTrackedTimeInInterval(start, end);
      }
    return retval;
  };

};  // end class TrackDB



class DetectionDB
{
private:
public:
  std::vector<Detection> detections;
  DetectionDB() : detections() {};
};
  

class UdfSubInterval
{
public:
  double start;
  double end;
  // net unused detections
  int count;
  // total detections
  int totDetections;
  UdfSubInterval() : count(0), start(0), end(0), totDetections(0) {};
  void add(int val)
  { count += val; };
  void addTot(int val)
  { cout << "addTot" << endl; totDetections += val; }
  bool isInInterval(double ts)
  { return ( (ts >= start) && (ts < end) ); };
};

class UdfInterval
{
public:
  UdfSubInterval *subIntervals;
  int numSubIntervals;
  int firstSub;
  int lastSub;
  int nextSub;
  double intervalWidth;
  double subIntervalWidth;
  // number of subIntervals to create ahead of current interval, to avoid losing data
  int buffer;
  UdfInterval() : subIntervals(NULL), numSubIntervals(0), firstSub(0), lastSub(0), nextSub(0), intervalWidth(0.0), subIntervalWidth(0.0) 
  {
    buffer = 5;
  };
  ~UdfInterval()
  {
    delete [] subIntervals;
  };
  
  // length in seconds
  void init(int length, int numSubs)
  {
    subIntervalWidth = (int) ((double) length / (double) numSubs);
    numSubIntervals = numSubs;
    intervalWidth = subIntervalWidth * numSubs;
    // allocate nubintervals to fill the interval, plus one more to fill the newest while the current is being calculated.
    subIntervals = new UdfSubInterval[numSubs + buffer];
    firstSub = 0;
    lastSub = numSubs - 1;
    nextSub = numSubs;
    cout << "UDF IntervalData: " << subIntervalWidth << " " <<  numSubIntervals << " " << intervalWidth << endl;
  };

  void initSubIntervals(double firstTimestamp)
  {
    double siStart = firstTimestamp;
    for (int i = 0; i < numSubIntervals + buffer; i++)
      {
	subIntervals[i].start = siStart;
	siStart = siStart + subIntervalWidth;
	subIntervals[i].end = siStart;
      }
    // printSubIntervals();
  };

  void printSubIntervals()
  {
    cout << "Subinterval  Start  End" << endl;
    int c = 0;
    int totalSubIntervals = numSubIntervals + buffer;
    int i = nextSub;
    while ( c < totalSubIntervals )
      {
	i = (firstSub + c) %  totalSubIntervals;
	cout << i << " " << subIntervals[i].start << " " << subIntervals[i].end << " " << 
	  subIntervals[i].count << " " << subIntervals[i].totDetections << endl;
	c++;
      }
  }
  
  UdfSubInterval *findSubInterval(double ts)
  {
    UdfSubInterval * retval = NULL;
    // assume its going into the next sub
    int c = 0;
    int totalSubIntervals = numSubIntervals + buffer;
    int i = lastSub;
    while ( c < totalSubIntervals && retval == NULL)
      {
	if (subIntervals[i].isInInterval(ts))
	  {
	    retval = &(subIntervals[i]);
	  }
	c++;
	i = (lastSub + c) %  totalSubIntervals;
      }
    return retval;
  }
  
  void addToSub(double ts, int val)
  {
    UdfSubInterval *si = findSubInterval(ts);
    if (si != NULL)
      {
	cout << "Adding " << val << " detection" << ((abs(val)>1) ? "s ":" ") << " at ts " << ts << " to interval " << si->start <<  endl;
	si->add(val);
	// only add raw detections to total detections
	// detection -> val==1, report->val==-1, first report->val==-nscan
	if (val == 1)
	  {
	    si->addTot(val);
	  }
      }
    else
      {
	// error
	std::cout << "ERROR: Could not find sub interval for timestamp " << ts << std::endl;
      }
    // printSubIntervals();
  };
  
  int computeInterval()
  {
    int retval = 0;
    int totalSubIntervals = numSubIntervals + buffer;
    if (numSubIntervals != 0)
      {
	for (int i = 0; i < numSubIntervals; i++)
	  {
	    int idx = (firstSub + i) %  totalSubIntervals;
	    retval += subIntervals[idx].count;
	    cout << "SubInterval " << idx << " start " << subIntervals[idx].start << " count " << subIntervals[idx].count << endl;
	  }
      }
    return retval;
  };
  
  int computeTotInterval()
  {
    int retval = 0;
    int totalSubIntervals = numSubIntervals + buffer;
    if (numSubIntervals != 0)
      {
	for (int i = 0; i < numSubIntervals; i++)
	  {
	    int idx = (firstSub + i) %  totalSubIntervals;
	    retval += subIntervals[idx].totDetections;
	    cout << "SubInterval " << idx << " start " << subIntervals[idx].start << " totDetections " << subIntervals[idx].totDetections << endl;
	  }
      }
    return retval;
  };

  void advance()
  {
    if (numSubIntervals != 0)
      {
	int endSub = (firstSub - 1 + numSubIntervals + buffer) % (numSubIntervals + buffer);
	subIntervals[firstSub].start = subIntervals[endSub].end;
	subIntervals[firstSub].end = subIntervals[firstSub].start + subIntervalWidth;
	subIntervals[firstSub].count = 0;
	subIntervals[firstSub].totDetections = 0;
	
	firstSub = (firstSub + 1) % (numSubIntervals + buffer);
	lastSub = (lastSub + 1) % (numSubIntervals + buffer);
	nextSub = (nextSub + 1) % (numSubIntervals + buffer);
      }
    // printSubIntervals();
  };
};  // end class UdfInterval


//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

DetectionDB db;
TrackDB tdb;
UdfInterval udfInterval;


void addDetection(double ts, double lat, double lon, double alt, double snr)
{
  DetectionDB *ddb = (DetectionDB *) &db;
  if (lon > 180.0)
    {
      lon = lon - 360;
    }
  Detection *d = new Detection(ts, lat, lon, alt, snr);
  // std::cout << "Adding Detection#" << ddb->detections.size() << " " << ts << " " << lat  << " " << lon << std::endl;
  
  ddb->detections.push_back(*d);
}

void removeDetection(double ts, double lat, double lon, double alt)
{
  DetectionDB *ddb = (DetectionDB *)  &db;
  vector<Detection>::iterator i;
  // std::cout << "Removing Detection " << ts << " " << lat  << " " << lon << std::endl;
  for (i = ddb->detections.begin(); i != ddb->detections.end(); i++)
    {
      if ((*i).ts == ts
	  && (*i).lat == lat 
	  && (*i).lon == lon
	  // && (*i).alt == alt
	  )
	{
	  // ddb->detections.erase(i);
	  break;
	}
    }
}

void clearDetections()
{
  DetectionDB *ddb = (DetectionDB *)  &db;  
  ddb->detections.clear();
}

int getNumUnused(int dummy)
{
  DetectionDB *ddb = (DetectionDB *)  &db;
  std::cout << "#Unused Detections=" << ddb->detections.size() << std::endl;
  return   ddb->detections.size();
}

void addReport(double ts, int id, double lat, double lon, double alt, double vlat, double vlon, double valt, void *monp)
{
  tdb.addReport(ts, id, lat, lon, alt, vlat, vlon, valt, monp);
}

/**
 *  Compute the average SNR over a time period
 */
void computeMeanSnr(double start, double end, void *monp)
{
  UdfMonitor *monitor = (UdfMonitor *) monp;
  DetectionDB *ddb = (DetectionDB *)  &db;
  vector<Detection>::iterator i;
  double sum = 0.0;
  int count = 0;

  double s = start/1000.0;
  double e = end/1000.0;
  for (i = ddb->detections.begin(); i != ddb->detections.end(); i++)
    {
      if ((*i).ts >= s && (*i).ts < e)
	{
	  sum += (*i).snr;
	  count++;
	}
    }
  double meanSnr = -1;
  
  if (count > 0)
    {
      meanSnr = sum / count;
    }
  monitor->intervalMeanSnr = meanSnr;

  cout << "SNR: " << monitor->intervalMeanSnr << " db size= " << ddb->detections.size()
       << " count " << count
       << endl;
}



//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  UDF Metrics

void initUdf(void *monp)
{
  UdfMonitor *monitor = (UdfMonitor *) monp;
  cout << "NScan=" << monitor->trackerNScan << endl;
  udfInterval.init(monitor->udfIntervalLength, monitor->udfNumSubIntervals);
}

void startUdfMonitor(double ts)
{
  udfInterval.initSubIntervals(ts);
}

void addToSubInterval(double ts, int val)
{
  cout << "addToSubInterval (detection)" << endl;
  udfInterval.addToSub(ts, val);
}

void addTrackReport(double ts, int trackId, void *monp)
{
  // cout << "addTrackReport" << endl;
  int val = -1;
  // if it is a new track, use nscan value
  Track *track = tdb.getTrack(trackId);
  UdfMonitor *monitor = (UdfMonitor *) monp;
  if (track == NULL)
    {
      val = -1 * monitor->trackerNScan;
    }
  else
    {
      if (track->reports.size() > 0)
	{
	  double firstTs = (track->reports[0])->time;
	  if (ts == firstTs)
	    {
	      val = -1 * monitor->trackerNScan;
	    }
	}
      else
	{
	      val = -1 * monitor->trackerNScan;
	}
    }
  udfInterval.addToSub(ts, val);
}


int udfComputeIntervalMetric(void *monp)
{
  UdfMonitor *monitor = (UdfMonitor *) monp;
  monitor->numUnassociated = udfInterval.computeInterval();
  monitor->totalDetections = udfInterval.computeTotInterval();
  monitor->percentUnassociatedDetections = 0.0;
  if (monitor->totalDetections > 0)
    {
      monitor->percentUnassociatedDetections = 100 * ((double) monitor->numUnassociated / (double) monitor->totalDetections);
    }
  double start = udfInterval.subIntervals[udfInterval.firstSub].start;
  double end = udfInterval.subIntervals[udfInterval.lastSub].end;
  
  udfInterval.advance();
  
  cout << "udf metrics for interval \t" << start <<  "-" << end << "\t"
       << monitor->numUnassociated << "\t" << monitor->totalDetections << "\t" << monitor->percentUnassociatedDetections << endl;
}




double toDegrees(double radians)
{
  double retval = (radians * 180.0) / M_PI;
  return retval;
}



double toRadians(double degrees)
{
  double retval = M_PI * (degrees / 180.0);
  return retval;
}

// great circle distance, over the earth's surface
// in meters
double calcDistance(double lat1, double lon1, double lat2, double lon2)
{
  double retval = 0;
  double rlat1 = toRadians(lat1);
  double rlat2 = toRadians(lat2);
  double rlon1 = toRadians(lon1);
  double rlon2 = toRadians(lon2);
  double dlat = rlat2 - rlat1;
  double dlon = rlon2 - rlon1;
  double delatLatSin = sin(dlat / 2.0);
  double deltaLonSin = sin(dlon / 2.0);
  double a = (delatLatSin * delatLatSin) + (cos(rlat1) * cos(rlat2) * deltaLonSin * deltaLonSin);
  double c = 2.0 * atan2(sqrt(a), sqrt(1-a));
  double d = c * earthRadius;
  retval = d;
  return retval;
}


// an approximation of great circle distance that is close for small distances
// and performs better
// in meters
double calcDistance2(double lat1, double lon1, double lat2, double lon2)
{
  double retval = 0;
  double rlat1 = toRadians(lat1);
  double rlat2 = toRadians(lat2);
  double rlon1 = toRadians(lon1);
  double rlon2 = toRadians(lon2);
  double x = (rlon2 - rlon1) * cos((rlat1 + rlat2) / 2.0);
  double y = rlat2 - rlat1;
  double d = earthRadius * sqrt((x * x) + (y * y));
  retval = d;
  return retval;
}


/**
 * compute the net 3d acceleration vector, in polar (a, az, el)
 */
void calcAccel(TrackReport *from, TrackReport *to, double *accel, double *az, double *el)
{
  double dvlat = to->vlat - from->vlat;
  double dvlon = to->vlon - from->vlon;
  double dvalt = to->valt - from->valt;
  double dt    = to->time - from->time;

  double alat = 0.0;
  double alon = 0.0;
  double aalt = 0.0;

  if (dt != 0.0)
    {
      alat = dvlat / dt;
      alon = dvlon / dt;
      aalt = dvalt / dt;
    }
  
  *accel = sqrt( (alat * alat) + (alon * alon) + (aalt * aalt) );
  *az = 0.0;
  if (alon != 0.0)
    {
      *az = atan(alat / alon);
      *az = toDegrees(*az);
    }
  *el = 0.0;
  if (*accel != 0.0)
    {
      *el = asin(aalt / (*accel));
      *el = toDegrees(*el);
    }
}



static double internalLastTime = 0.0;
void reportTrackMetrics(double lastTime, double interval, void* monp)
{
  UdfMonitor *monitor = (UdfMonitor *) monp;
  double start = lastTime - monitor->interval; // internalLastTime / 1000;
  double end = start + monitor->interval;  // lastTime / 1000;
  start /= 1000;
  end /= 1000;
  internalLastTime = lastTime;
  int numTracks = tdb.getTotalTracks();
  int numTracksInInterval = tdb.getTracksInInterval(start, end);
  double trackDistance = tdb.getTotalTrackDistance();
  double intervalTrackDistance = tdb.getTotalTrackDistanceInterval(start, end);
  double trackTime = tdb.getTotalTrackTime();
  double intervalTrackTime = tdb.getTotalTrackTimeInterval(start, end);

  // ???? these need to get into the SMEDL event stream
  // and to the run-time graph visualizer
  std::cout << "Metrics for interval " << start << " - " << end << "\n" <<
    "\t numTracks = " << numTracks << "\n" <<
    "\t numTracksInInterval = " << numTracksInInterval << "\n" <<
    "\t trackDistance = " << trackDistance << "\n" <<
    "\t intervalTrackDistance = " << intervalTrackDistance << "\n" <<
    "\t intervalTrackTime = " << intervalTrackTime << "\n" <<
    std::endl;

  if (numTracksInInterval > 0)
    {
      monitor->timePerTrack = intervalTrackTime / numTracksInInterval;
      monitor->distancePerTrack = intervalTrackDistance / numTracksInInterval;
    }
  else
    {
      monitor->timePerTrack  = 0.0;
      monitor->distancePerTrack  = 0.0;
    }

  cout << "ObsTimePerTrack % Metric: " <<  100.0 * (monitor->timePerTrack / (monitor->interval / 1000.0) ) << endl;
}




void unittest(char *filename, UdfMonitor *monitor)
{

  double start = 0;
  double end = 0;

  ifstream fin;
  fin.open(filename);
  
  fin >> start;
  fin >> end;
  while (fin.good())
    {
      double ts = 0;
      int id = 0;
      double lat = 0;
      double lon = 0;
      double alt = 0;
      fin >> id >> ts >> lat >> lon >> alt;
      if (id != 0)
	{
	  addReport(ts, id, lat, lon, alt, 0, 0, 0, NULL);
	}
    }
  // reportTrackMetrics(lastTime, interval, (void *) monitor);
  int numTracks = tdb.getTotalTracks();
  int numTracksInInterval = tdb.getTracksInInterval(start, end);
  double trackDistance = tdb.getTotalTrackDistance();
  double intervalTrackDistance = tdb.getTotalTrackDistanceInterval(start, end);
  double trackTime = tdb.getTotalTrackTime();
  double intervalTrackTime = tdb.getTotalTrackTimeInterval(start, end);

  // ???? these need to get into the SMEDL event stream
  // and to the run-time graph visualizer
  std::cout << "Metrics for interval " << start << " - " << end << "\n" <<
    "\t numTracks = " << numTracks << "\n" <<
    "\t numTracksInInterval = " << numTracksInInterval << "\n" <<
    "\t trackDistance = " << trackDistance << "\n" <<
    "\t intervalTrackDistance = " << intervalTrackDistance << "\n" <<
    "\t intervalTrackTime = " << intervalTrackTime << "\n" <<
    std::endl;
    
  fin.close();
}


