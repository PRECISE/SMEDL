## Makefile for Explorer test case
CC = gcc
CFLAGS = -g -Wall -std=c99
HDRS = explorer.h
SRCS = explorer.c explorer_mon.c

## This assigns the object file names to match the .c files
OBJS = $(SRCS:.c=.o)

## These define the rules to make each version
non-instrumented : explorer.o
	$(CC) $(CFLAGS) explorer.o -o explorer

instrumented : explorer.o explorer_mon.o
	$(CC) $(CFLAGS) explorer.o explorer_mon.o -o explorer-instrumented

## Source file rules
explorer.o : explorer.c explorer.h
	$(CC) $(CFLAGS) -c explorer.c
	
explorer_mon.o : explorer_mon.c explorer.h
	$(CC) $(CFLAGS) -c explorer_mon.c

## Remove all intermediate and executable files
clean :
	rm -f explorer explorer-instrumented $(OBJS)
