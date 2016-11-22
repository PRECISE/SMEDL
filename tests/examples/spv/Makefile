# Makefile for building the Spv monitor.

all:
	gcc -o bin/monitor -Wall -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -std=c99 monitor.c gen/actions.c gen/cJSON.c gen/monitor_map.c gen/amqp_utils.c gen/mon_utils.c gen/spv_mon.c
clean:
	rm bin/*
