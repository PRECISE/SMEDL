# Makefile for building the atif monitor.

all:
	gcc gen/string_mon.c gen/string_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c -Wall  -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/string_test

	gcc gen/stringVariableUpdate_mon.c gen/string_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c -Wall  -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/string_test2

	gcc gen/stringLiteral_mon.c gen/stringLiteral_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c -Wall  -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/stringLiteral_test

	gcc gen/stringLiteral2_mon.c gen/stringLiteral_monitor.c gen/amqp_utils.c gen/monitor_map.c gen/actions.c gen/cJSON.c gen/mon_utils.c -Wall  -L/usr/local/lib -lrabbitmq -lconfig -I/usr/local/include -o bin/stringLiteral_test2


clean:
	rm bin/*
