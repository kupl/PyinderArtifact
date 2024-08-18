#!/bin/sh

cd $1
export PYTHONPATH="$HOME/Pyinder/..:$PYTHONPATH"
timeout 7200 python -m Pyinder.client.pyre -n --output=json mine