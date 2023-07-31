#!/bin/bash

invfile='../../../invariant.txt'
progfile=`head -1 $invfile`
echo "$progfile, $invfile"

if [[ $1 == "--show" ]]; then
	cat $progfile
	cat $invfile
elif [[ $1 == "--verify" ]]; then
	cat $invfile
	python3 driver.py $progfile $invfile
else
	echo "Usage: check_invariant [--show|--verify]"
fi
