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
COMMONOBJS=actions.o amqp_utils.o cJSON.o monitor_map.o mon_utils.o
SOURCES:=$(wildcard *.c)

########################################
# Rules

all: multiAverages

.PHONY: all clean

clean:
	rm -f *.d *.o multiAverages

multiAverages: $(COMMONOBJS) frontend_mon.o frontend_monitor_wrapper.o averager_mon.o averager_monitor_wrapper.o sumMonitor_global_wrapper.o
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

