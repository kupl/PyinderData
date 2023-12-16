#!/bin/sh

cd $1
PYTHONPATH="/home/wonseok/Pyinder/..:$PYTHONPATH"
timeout 10800 python -m Pyinder.client.pyre -n --output=json mine