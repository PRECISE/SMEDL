#include <math.h>

static const double earthRadius = 6371000;

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


double calcBound(double lat1, double lon1, double lat2, double lon2, double end, double ts1, double ts2){
    double distToNextPoint= calcDistance(lat1, lon1, lat2, lon2);
    double iterpolation = (end - ts1) / (ts2 - ts1);
    double distFromIntervalEndToLastPoint = distToNextPoint * iterpolation;
    return distFromIntervalEndToLastPoint;
    
}


