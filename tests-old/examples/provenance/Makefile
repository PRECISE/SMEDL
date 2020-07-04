# Makefile for building the atif monitor.

all:
	gcc gen/stringRate_mon.c gen/stringRate_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c -Wall  -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/stringRate

	gcc gen/stringThresh_mon.c gen/thresh_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c  -Wall -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/stringThresh

	gcc gen/adaptationTrigger_mon.c gen/adaptationTrigger_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c  -Wall -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/adaptationTrigger

clean:
	rm bin/*
