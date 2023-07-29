#!/bin/sh

invfile='../../../invariant.txt'
progfile=`head -1 $invfile`
echo "$progfile, $invfile"
cat $invfile
python3 driver.py $progfile $invfile
