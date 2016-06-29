how to compile:

gcc -o explorer_mon -L/usr/local/lib -lrabbitmq  -I/usr/local/include -std=c99 actions.c monitor_map.c explorer_mon.c helper.c explorer_multi.c utils.c

how to execute:

./explorer_mon [# of threads]