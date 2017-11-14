CC = gcc
CFLAGS = -DMEMLIM=6144 -O2 -DXUSAFE -DNOREDUCE
SAFETY = -DSAFETY -DNOCLAIM -DNOFAIR
FAIR = -DNFAIR=3
SRCDIR = ./src
RLBLDIR = ./src/relabel
BINDIR = ./bin
# compile options for scenario C
LMMT = -DMA=83		# Less Memory, More Time
MMLT = -DCOLLAPSE	# More Memory, Less Time

checkdir:
	@if [ ! -d $(SRCDIR) ]; then \
	echo "Source directory $(SRCDIR) not found"; \
	exit 1; \
	fi
	@if [ ! -d $(BINDIR) ]; then \
	mkdir $(BINDIR); \
	echo "Output directory $(BINDIR) created"; \
	fi

checkdirrelabel:
	@if [ ! -d $(RLBLDIR) ]; then \
	echo "Source directory $(RLBLDIR) not found"; \
	exit 1; \
	fi
	@if [ ! -d $(BINDIR) ]; then \
	mkdir $(BINDIR); \
	echo "Output directory $(BINDIR) created"; \
	fi


# scenario A
ASafe:
	@make checkdir
	spin -a $(SRCDIR)/CarEmA.pml
	$(CC) $(CFLAGS) $(SAFETY) -o $(BINDIR)/panASafe pan.c

A:
	@make checkdir
	spin -a $(SRCDIR)/CarEmA.pml
	$(CC) $(CFLAGS) -o $(BINDIR)/panA pan.c

AMultiSafe:
	@make checkdir
	spin -a -DMULTI $(SRCDIR)/CarEmA.pml
	$(CC) $(CFLAGS) $(SAFETY) -o $(BINDIR)/panAMultiSafe pan.c

AMulti:
	@make checkdir
	spin -a -DMULTI $(SRCDIR)/CarEmA.pml
	$(CC) $(CFLAGS) -o $(BINDIR)/panAMulti pan.c

# scenario B
B:
	@make checkdir
	spin -a $(SRCDIR)/CarEmB.pml
	$(CC) $(CFLAGS) -o $(BINDIR)/panB pan.c

BFair:
	@make checkdir
	spin -a $(SRCDIR)/CarEmB.pml
	$(CC) $(CFLAGS) $(FAIR) -o $(BINDIR)/panBFair pan.c

BProgressAll:
	@make checkdir
	spin -a -DALL $(SRCDIR)/CarEmBprogress.pml
	$(CC) $(CFLAGS) -DNP -o $(BINDIR)/panBProgAll pan.c

BProgress:
	@make checkdir
	spin -a $(SRCDIR)/CarEmBprogress.pml
	$(CC) $(CFLAGS) -DNP -o $(BINDIR)/panBProg pan.c

BProgressAllFair:
	@make checkdir
	spin -a -DALL $(SRCDIR)/CarEmBprogress.pml
	$(CC) $(CFLAGS) -DNP $(FAIR) -o $(BINDIR)/panBProgAllFair pan.c

BProgressFair:
	@make checkdir
	spin -a $(SRCDIR)/CarEmBprogress.pml
	$(CC) $(CFLAGS) -DNP $(FAIR) -o $(BINDIR)/panBProgFair pan.c

# scenario C
C:
	@make checkdir
	spin -a $(SRCDIR)/CarEmC.pml
	$(CC) $(CFLAGS) $(MMLT) -o $(BINDIR)/panC pan.c

CFair:
	@make checkdir
	spin -a $(SRCDIR)/CarEmC.pml
	$(CC) $(CFLAGS) $(FAIR) $(MMLT) -o $(BINDIR)/panCFair pan.c

CG:
	@make checkdir
	spin -a -DGARAGE1 -DGARAGE2 -DTOWTRUCK $(SRCDIR)/CarEmC.pml
	$(CC) $(CFLAGS) $(MMLT) -o $(BINDIR)/panCG pan.c

CTT:
	@make checkdir
	spin -a -DCES1 -DGARAGE1 -DTOWTRUCK $(SRCDIR)/CarEmC.pml
	$(CC) $(CFLAGS) $(MMLT) -o $(BINDIR)/panCTT pan.c

CTTFair:
	@make checkdir
	spin -a -DCES1 -DGARAGE1 -DTOWTRUCK $(SRCDIR)/CarEmC.pml
	$(CC) $(CFLAGS) $(FAIR) $(MMLT) -o $(BINDIR)/panCTTfair pan.c

CRC:
	@make checkdir
	spin -a -DCES1 -DGARAGE1 -DRENTALCAR $(SRCDIR)/CarEmC.pml
	$(CC) $(CFLAGS) $(MMLT) -o $(BINDIR)/panCRC pan.c

CTTProgressAll:
	@make checkdir
	spin -a -DALL -DCES2 -DGARAGE1 -DTOWTRUCK $(SRCDIR)/CarEmCprogress.pml
	$(CC) $(CFLAGS) $(MMLT) -DNP -o $(BINDIR)/panCProgAll pan.c

CTTProgress:
	@make checkdir
	spin -a -DCES2 -DGARAGE1 -DTOWTRUCK $(SRCDIR)/CarEmCprogress.pml
	$(CC) $(CFLAGS) $(MMLT) -DNP -o $(BINDIR)/panCProg pan.c

CTTProgressAllFair:
	@make checkdir
	spin -a -DALL -DCES2 -DGARAGE1 -DTOWTRUCK $(SRCDIR)/CarEmCprogress.pml
	$(CC) $(CFLAGS) $(MMLT) -DNP $(FAIR) -o $(BINDIR)/panCProgAllFair pan.c

CTTProgressFair:
	@make checkdir
	spin -a -DCES2 -DGARAGE1 -DTOWTRUCK $(SRCDIR)/CarEmCprogress.pml
	$(CC) $(CFLAGS) $(MMLT) -DNP $(FAIR) -o $(BINDIR)/panCProgFair pan.c

# scenario C "relabel"
CRelabel:
	@make checkdirrelabel
	spin -a $(RLBLDIR)/CarEmC_relabel.pml
	$(CC) $(CFLAGS) $(LMMT) -o $(BINDIR)/panCRel pan.c

CRelabelFair:
	@make checkdirrelabel
	spin -a $(RLBLDIR)/CarEmC_relabel.pml
	$(CC) $(CFLAGS) $(LMMT) $(FAIR) -o $(BINDIR)/panCRelFair pan.c

CRelabelProgressAll:
	@make checkdirrelabel
	spin -a -DALL $(RLBLDIR)/CarEmCprogress_relabel.pml
	$(CC) $(CFLAGS) $(LMMT) -DNP -o $(BINDIR)/panCRelProgAll pan.c

CRelabelProgress:
	@make checkdirrelabel
	spin -a $(RLBLDIR)/CarEmCprogress_relabel.pml
	$(CC) $(CFLAGS) $(LMMT) -DNP -o $(BINDIR)/panCRelProg pan.c

CRelabelProgressAllFair:
	@make checkdirrelabel
	spin -a -DALL $(RLBLDIR)/CarEmCprogress_relabel.pml
	$(CC) $(CFLAGS) $(LMMT) -DNP $(FAIR) -o $(BINDIR)/panCRelProgAllFair pan.c

CRelabelProgressFair:
	@make checkdirrelabel
	spin -a $(RLBLDIR)/CarEmCprogress_relabel.pml
	$(CC) $(CFLAGS) $(LMMT) -DNP $(FAIR) -o $(BINDIR)/panCRelProgFair pan.c

.PHONY : clean
clean :
	-@rm pan*
	-@rm _spin_nvr.tmp

.PHONY : clean_trail
clean_trail :
	-@rm *.pml.trail

.PHONY : clean
clean_bin :
	-@rm $(BINDIR)/*
