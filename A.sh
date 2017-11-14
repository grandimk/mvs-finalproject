#!/bin/bash
BIN=./bin
RESULT=./result
if [ ! -d $RESULT ]; then
	mkdir $RESULT;
	echo "Result directory $RESULT created";
fi
START=$(date +%s)
echo "Generate the verifier for scenario A Safe..."
make ASafe
	echo "Test invalid-end states for scenario A:"
	time ($BIN/panASafe) > $RESULT/ASafe
make clean
echo "Generate the verifier for scenario A..."
make A
	echo "Test property (a) for scenario A:"
	time ($BIN/panA -a -N prop_a) > $RESULT/A_prop_a
	echo "Test property (b) for scenario A:"
	time ($BIN/panA -a -N prop_b) > $RESULT/A_prop_b
	echo "Test property (c) for scenario A:"
	time ($BIN/panA -a -N prop_c) > $RESULT/A_prop_c
make clean
# con due istanze di officine e carro attrezzi
echo "Generate the verifier for scenario A Multi (-DMULTI) Safe..."
make AMultiSafe
	echo "Test invalid-end states for scenario A Multi:"
	time ($BIN/panAMultiSafe) > $RESULT/AMultiSafe
make clean
echo "Generate the verifier for scenario A Multi (-DMULTI)..."
make AMulti
	echo "Test property (a) for scenario A Multi:"
	time ($BIN/panAMulti -a -N prop_a) > $RESULT/AMulti_prop_a
	echo "Test property (b) for scenario A Multi:"
	time ($BIN/panAMulti -a -N prop_b) > $RESULT/AMulti_prop_b
	echo "Test property (c) for scenario A Multi:"
	time ($BIN/panAMulti -a -N prop_c) > $RESULT/AMulti_prop_c
make clean
END=$(date +%s)
echo "Verification scenario A completed"
DIFF=$(echo "$END - $START" | bc)
echo "Total time: $DIFF seconds"
