CC=gcc
CPPFLAGS=
CFLAGS=
LDFLAGS=
LDLIBS=

# Uncomment for debug build:
#CFLAGS=-g -DDEBUG $(CFLAGS)

########################################
# Required variables

CPPFLAGS:=-D_XOPEN_SOURCE=500 $(CPPFLAGS)
CFLAGS:=-std=c99 $(CFLAGS)
LDLIBS:=$(LDLIBS) -lm -lconfig -lrabbitmq
#COMMONOBJS=actions.o amqp_utils.o cJSON.o monitor_map.o mon_utils.o
COMMONOBJS=actions.o monitor_map.o mon_utils.o
#SOURCES:=actions.c amqp_utils.c cJSON.c monitor_map.c mon_utils.c auctionmonitor_global_wrapper.c auctionmonitor_mon.c auctionmonitor_monitor_wrapper.c 
SOURCES:=actions.c monitor_map.c mon_utils.c auctionmonitor_global_wrapper.c auctionmonitor_mon.c auctionmonitor_monitor_wrapper.c main.c

########################################
# Rules

all: auction 

.PHONY: all clean

clean:
	rm -f *.d *.o auction 

auction: $(COMMONOBJS) auctionmonitor_mon.o auctionmonitor_monitor_wrapper.o auctionmonitor_global_wrapper.o main.o
	$(CC) $(CFLAGS) $(LDFLAGS) $+ $(LDLIBS) -o $@

### The rest of the makefile is for automatically handling header dependencies

%.d: %.c
	@set -e; rm -f $@; \
	$(CC) -M $(CPPFLAGS) $< > $@.$$$$; \
	sed 's,\($*\)\.o[ :]*,\1.o $@ : ,g' < $@.$$$$ > $@; \
	rm -f $@.$$$$

$(info ** Note: Messages saying "*.d: No such file or directory" are okay. The files will)
$(info **       be automatically generated.)
include $(SOURCES:.c=.d)
