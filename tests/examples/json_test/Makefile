# Makefile for building the atif monitor.

all:
	gcc gen/json_mon.c gen/json_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c -Wall  -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/json


clean:
	rm bin/*
