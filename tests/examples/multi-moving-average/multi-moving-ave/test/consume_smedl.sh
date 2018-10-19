#!/bin/sh

amqp-consume -e "smedl.topic" -r "#" cat
