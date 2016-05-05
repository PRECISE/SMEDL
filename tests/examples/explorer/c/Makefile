## Makefile for Explorer test case
CC = gcc
CFLAGS = -g -Wall -std=c99
HDRS = explorer_multi.h
SRCS = explorer_multi.c explorer_mon.c
BIN_DIR = bin

## This assigns the object file names to match the .c files
#OBJS = $(SRCS:.c=.o)

## These define the rules to make each version
non-instrumented : explorer_multi.o
	$(CC) $(CFLAGS) $(BIN_DIR)/explorer_multi.o -o $(BIN_DIR)/explorer

instrumented : explorer_multi.o explorer_mon.o
	$(CC) $(CFLAGS) $(BIN_DIR)/explorer_multi.o $(BIN_DIR)/explorer_mon.o helper.c -o $(BIN_DIR)/explorer-instrumented

## Source file rules
explorer_multi.o : explorer_multi.c explorer_multi.h
	$(CC) $(CFLAGS) -c explorer_multi.c -o $(BIN_DIR)/explorer_multi.o

explorer_mon.o : explorer_mon.c explorer_multi.h
	$(CC) $(CFLAGS) -c explorer_mon.c -o $(BIN_DIR)/explorer_mon.o

## Remove all intermediate and executable files
clean :
	rm -f $(BIN_DIR)/explorer $(BIN_DIR)/explorer-instrumented $(BIN_DIR)/explorer.o $(BIN_DIR)/explorer_mon.o
