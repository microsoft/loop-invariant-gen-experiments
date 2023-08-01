#!/bin/bash

invfile='../../../invariant.txt'
progfile=`head -1 $invfile`
echo "$progfile, $invfile"

if [[ $1 == "--show" ]]; then
	cat $progfile
	cat $invfile
elif [[ $1 == "--invariant" ]]; then
	cat $invfile
	python3 driver.py $progfile $invfile "invariant"
elif [[ $1 == "--variant" ]]; then
	cat $invfile
	python3 driver.py $progfile $invfile "variant"
else
	echo "Usage: check_invariant [--show|--invariant|--variant]"
fi
