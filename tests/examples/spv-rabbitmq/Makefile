# Makefile for building the Spv monitor.

all:
	gcc -o bin/monitor -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -std=c99 monitor.c gen/actions.c gen/monitor_map.c gen/utils.c gen/spv_mon.c
clean:
	rm bin/*
