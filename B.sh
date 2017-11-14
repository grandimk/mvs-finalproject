#!/bin/bash
BIN=./bin
RESULT=./result
if [ ! -d $RESULT ]; then
	mkdir $RESULT;
	echo "Result directory $RESULT created";
fi
START=$(date +%s)
echo "Generate the verifier for scenario B..."
make B
	echo "Test property (d) for scenario B:"
	time ($BIN/panB -m100000 -a -N prop_d) > $RESULT/B_prop_d
	echo "Test property (e) for scenario B:"
	time ($BIN/panB -m100000 -a -N prop_e) > $RESULT/B_prop_e
make clean
# proprietà f (richiede weak fairness)
echo "Generate the verifier for scenario B with weak fairness assumption..."
make BFair
	echo "Test property (f) for scenario B Fair:"
	time ($BIN/panBFair -m100000 -a -f -N prop_e) > $RESULT/B_prop_f
make clean
# proprietà g (prevede due casi, ognuno con e senza weak fairness)
echo "Generate the verifier for scenario B All (-DALL)..."
make BProgressAll
	echo "Test property (g) for scenario B All:"
	time ($BIN/panBProgAll -m100000 -l) > $RESULT/BAll_prop_g
make clean
echo "Generate the verifier for scenario B..."
make BProgress
	echo "Test property (g) for scenario B:"
	time ($BIN/panBProg -m100000 -l) > $RESULT/B_prop_g
make clean
# con weak fairness
echo "Generate the verifier for scenario B All (-DALL) with weak fairness assumption..."
make BProgressAllFair
	echo "Test property (g) for scenario B All Fair:"
	time ($BIN/panBProgAllFair -m100000 -l -f) > $RESULT/BAllFair_prop_g
make clean
echo "Generate the verifier for scenario B with weak fairness assumption..."
make BProgressFair
	echo "Test property (f) for scenario B Fair:"
	time ($BIN/panBProgFair -m100000 -l -f) > $RESULT/BFair_prop_g
make clean
END=$(date +%s)
echo "Verification scenario B completed"
DIFF=$(echo "$END - $START" | bc)
MIN=$(echo "$DIFF/60" | bc)
echo "Total time: $DIFF seconds ($MIN minutes)"