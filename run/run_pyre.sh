#!/bin/sh

cd $1
timeout 7200 pyre -n --output=json check