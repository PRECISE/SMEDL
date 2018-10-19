#!/usr/bin/env python3

from subprocess import call
from time import sleep
import sys

host = "localhost"
port = 5672
user = "guest"
passwd = "guest"
exchange = "smedl.topic"

# Used to set routing key in outgoung messages and determine what letter will
# be used in the progress bar. If the last part of the routing key is found in
# the body of the outgoing message, that routing key will be used.
# The values of the dict can be set to different characters to allow quick
# identification of what message types are going out.
progress_bar_letters = dict()
progress_bar_letters['ch1.measurement'] = '.'

fname = "test_input.json"
send_count_limit = -1
if len(sys.argv) > 1:
    fname = sys.argv[1]

if len(sys.argv) > 2:
    send_count_limit = int(sys.argv[2])

send_count = 0
def send_message(body):
    global host, port, user, passwd, exchange, rk, send_count
    rk = "#"
    for dict_rk in progress_bar_letters:
        if dict_rk.split('.')[-1] in body:
            rk = dict_rk
            print(progress_bar_letters[dict_rk], end="", flush=True)
        else:
            print('.', end="", flush=True)

    call(["./amqpsend", "-h", host, "-P", str(port), "-u", user, "-p", passwd, exchange, rk , body])

    send_count += 1
    if send_count % 50 == 0:
        print(" ", send_count, sep="", flush=True)
    
    if send_count == send_count_limit:
        raise StopException

    sleep(1.0)

class StopException(Exception):
    pass

with open(fname) as f:
    brace_depth = 0
    in_message = False
    message = ""

    try:
        for line in f:
            i = 0
            j = 0
            for char in line:
                j += 1
                if char == '{':
                    if in_message == False:
                        i = j - 1
                        in_message = True
                    brace_depth += 1
                elif char == '}':
                    brace_depth -= 1
                    if brace_depth == 0:
                        message += line[i:j]
                        in_message = False
                        send_message(message)
                        message = ""
            if in_message:
                message += line[i:]
                message += '\n'
    except StopException:
        pass

if send_count % 50 != 0:
    print(" ", send_count, sep="")
