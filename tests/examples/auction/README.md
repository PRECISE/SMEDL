Auction Example
===============

This monitor is based on a benchmark from the QEA project, described [here](http://crv.liflab.ca/wiki/index.php/Offline_Team2_Benchmark1). See that page for the full details, but the high level summary is that the goal is to monitor an auction system. Auctions are created with a minimum selling price (also called a "reserve" in our monitor) and a duration in days. In addition to the create_auction event, there are bid, sold, and end_of_day events. Bids must occur in strictly increasing order, items cannot be sold before they reach the minimum selling price (but must be sold if they do), and no further activity on an auction can happen once it expires. An auction expires after the appropriate number of end_of_day events.

This system is monitored by a single SMEDL monitor, `auctionmonitor`, with a new instance created for each auction. When a violation is detected, one of several alarm events gets raised (depending on what kind of violation it was).

This example is included for demonstration of the --nojson/-j option for mgen. To generate this monitor:

    mgen -j path-to-here/auctionmonitor --arch=path-to-here/auction

A driver (`main.c`) and makefile are provided for convenience for when using this option.

When running, the driver expects a trace file as the first argument. Test traces are in the `traces/` directory. The driver will print the number of events processed so far after every 100,000 events.

Sample trace files available:

* `auction_trace_invalid1`: An item is sold before it reaches the minimum selling price
* `auction_trace_invalid2`: An item is sold after it expires
* `auction_trace_invalid3`: An item is sold twice
