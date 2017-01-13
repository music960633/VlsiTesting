#

CFLAGS = -O2 -DNDEBUG

FILES = tpgmain.o input.o level.o sim.o podem.o test.o init_flist.o faultsim.o display.o tdfsim.o tdfatpg.o

TARGET=atpg

$(TARGET) : $(FILES) 
	gcc $(CFLAGS) $(FILES) -lm -o atpg

tpgmain.o : atpg.h miscell.h tpgmain.c
	gcc $(CFLAGS) -c tpgmain.c
input.o : atpg.h miscell.h input.c
	gcc $(CFLAGS) -c input.c
level.o : atpg.h miscell.h level.c
	gcc $(CFLAGS) -c level.c
sim.o : atpg.h miscell.h logic_tbl.h sim.c
	gcc $(CFLAGS) -c sim.c
podem.o : atpg.h miscell.h podem.c
	gcc $(CFLAGS) -c podem.c
init_flist.o : atpg.h miscell.h init_flist.c
	gcc $(CFLAGS) -c init_flist.c
faultsim.o : atpg.h miscell.h faultsim.c
	gcc $(CFLAGS) -c faultsim.c
test.o : atpg.h miscell.h test.c
	gcc $(CFLAGS) -c test.c
display.o : atpg.h miscell.h display.c
	gcc $(CFLAGS) -c display.c
tdfsim.o : atpg.h miscell.h tdfsim.c
	gcc $(CFLAGS) -c tdfsim.c
tdfatpg.o : atpg.h miscell.h tdfatpg.c
	gcc $(CFLAGS) -c tdfatpg.c
clean:
	rm $(TARGET) *.o
tags:
	ctags *.c *.h

