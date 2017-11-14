#!/bin/bash
BIN=./bin
RESULT=./result
if [ ! -d $RESULT ]; then
	mkdir $RESULT;
	echo "Result directory $RESULT created";
fi
if [ "$#" = "1" ] && [ "$1" = "relabel" ]; then
	START=$(date +%s)
	echo "Generate the verifier for scenario C Relabel..."
	make CRelabel
		echo "Test property (d) for scenario C:"
		time ($BIN/panCRel -m100000 -w26 -a -N prop_d) > $RESULT/CRelabel_prop_d
		echo "Test property (e) for scenario C:"
		time ($BIN/panCRel -m100000 -w26 -a -N prop_e) > $RESULT/CRelabel_prop_e
		echo "Test property (h) for scenario C:"
		time ($BIN/panCRel -m100000 -w26 -a -N prop_h) > $RESULT/CRelabel_prop_h
		echo "Test property (i) for scenario C:"
		time ($BIN/panCRel -m100000 -w26 -a -N prop_i) > $RESULT/CRelabel_prop_i
		echo "Test property (j) for scenario C:"
		time ($BIN/panCRel -m100000 -w26 -a -N prop_j) > $RESULT/CRelabel_prop_j
		echo "Test property (k) for scenario C:"
		time ($BIN/panCRel -m100000 -w26 -a -N prop_k) > $RESULT/CRelabel_prop_k
		echo "Test property (l) for scenario C:"
		time ($BIN/panCRel -m100000 -w26 -a -N prop_l) > $RESULT/CRelabel_prop_l
	make clean
	echo "Generate the verifier for scenario C Relabel with weak fairness assumption..."
	make CRelabelFair
		echo "Test property (f) for scenario C Fair:"
		time ($BIN/panCRelFair -m100000 -w26 -a -f -N prop_e) > $RESULT/CRelabel_prop_f
	make clean
	# proprietà g (prevede due casi, ognuno con e senza weak fairness)
	echo "Generate the verifier for scenario C Relabel All..."
	make CRelabelProgressAll
		echo "Test property (g) for scenario C All:"
		time ($BIN/panCRelProgAll -m100000 -w26 -l) > $RESULT/CRelabelAll_prop_g
	make clean
	echo "Compilo il programma Progress dello scenario C (relabel)..."
	make CRelabelProgress
		echo "Test property (g) for scenario C:"
		time ($BIN/panCRelProg -m100000 -w26 -l) > $RESULT/CRelabel_prop_g
	make clean
	# con weak fairness
	echo "Compilo il programma Progress dello scenario C (relabel) con -DALL e assunzioni di weak fairness..."
	make CRelabelProgressAllFair
		echo "Test property (g) for scenario C All Fair:"
		time ($BIN/panCRelProgAllFair -m100000 -w26 -l -f) > $RESULT/CRelabelAllFair_prop_g
	make clean
	echo "Compilo il programma Progress dello scenario C (relabel) con assunzioni di weak fairness..."
	make CRelabelProgressFair
		echo "Test property (g) for scenario C Fair:"
		time ($BIN/panCRelProgFair -m100000 -w26 -l -f) > $RESULT/CRelabelFair_prop_g
	make clean

	END=$(date +%s)
else
	START=$(date +%s)
	echo "Generate the verifier for scenario C (-DCES1 -DGARAGE1 -DTOWTRUCK)..."
	make CTT
		echo "Test property (d) for scenario C:"
		time ($BIN/panCTT -m100000 -w26 -a -N prop_d) > $RESULT/C_prop_d
		echo "Test property (e) for scenario C:"
		time ($BIN/panCTT -m100000 -w26 -a -N prop_e) > $RESULT/C_prop_e
		echo "Test property (i) for scenario C:"
		time ($BIN/panCTT -m100000 -w26 -a -N prop_i) > $RESULT/C_prop_i
		echo "Test property (j) for scenario C:"
		time ($BIN/panCTT -m100000 -w26 -a -N prop_j) > $RESULT/C_prop_j
		echo "Test property (k) for scenario C:"
		time ($BIN/panCTT -m100000 -w26 -a -N prop_k) > $RESULT/C_prop_k
	make clean
	echo "Generate the verifier for scenario C (-DGARAGE1 -DGARAGE2 -DTOWTRUCK)..."
	make CG
		echo "Test property (h) for scenario C:"
		time ($BIN/panCG -m100000 -w26 -a -N prop_h) > $RESULT/C_prop_h
	make clean
	echo "Generate the verifier for scenario C (-DCES1 -DGARAGE1 -DRENTALCAR)..."
	make CRC
		echo "Test property (l) for scenario C:"
		time ($BIN/panCRC -m100000 -w26 -a -N prop_l) > $RESULT/C_prop_l
	make clean
	echo "Generate the verifier for scenario C (-DCES1 -DGARAGE1 -DTOWTRUCK) with weak fairness assumption..."
	make CTTFair
		echo "Test property (f) for scenario C Fair:"
		time ($BIN/panCTTFair -m100000 -w28 -a -f -N prop_e) > $RESULT/C_prop_f
	make clean
	# proprietà g (prevede due casi, ognuno con e senza weak fairness)
	echo "Generate the verifier for scenario C (-DALL -DCES2 -DGARAGE1 -DTOWTRUCK)..."
	make CTTProgressAll
		echo "Test property (g) for scenario C All:"
		time ($BIN/panCProgAll -m100000 -w26 -l) > $RESULT/CAll_prop_g
	make clean
	echo "Generate the verifier for scenario C (-DCES2 -DGARAGE1 -DTOWTRUCK)..."
	make CTTProgress
		echo "Test property (g) for scenario C:"
		time ($BIN/panCProg -m100000 -w26 -l) > $RESULT/C_prop_g
	make clean
	# con weak fairness
	echo "Generate the verifier for scenario C (-DALL -DCES2 -DGARAGE1 -DTOWTRUCK) with weak fairness assumption..."
	make CTTProgressAllFair
		echo "Test property (g) for scenario C All Fair:"
		time ($BIN/panCProgAllFair -m100000 -w28 -l -f) > $RESULT/CAllFair_prop_g
	make clean
	echo "Generate the verifier for scenario C (-DCES2 -DGARAGE1 -DTOWTRUCK) with weak fairness assumption..."
	make CTTProgressFair
		echo "Test property (g) for scenario C Fair:"
		time ($BIN/panCProgFair -m100000 -w28 -l -f) > $RESULT/CFair_prop_g
	make clean
	END=$(date +%s)
fi
echo "Verification scenario C completed"
DIFF=$(echo "$END - $START" | bc)
MIN=$(echo "$DIFF/60" | bc)
echo "Total time: $DIFF seconds ($MIN minutes)"
