#!/bin/bash

trap "exit" INT

rm -f log
for file in ../benchmarks/icfp/*.sl; do
	echo "====================" >> log
	echo "START BENCHMARK: $file" >> log
	PYTHONPATH=$PYTHONPATH:../thirdparty/libeusolver/build/:../thirdparty/z3/build/:../thirdparty/bitstring-3.1.3/ timeout "$1" python3 solvers.py icfp $file log
	echo "END BENCHMARK: $file" >> log
	echo "====================" >> log
done
