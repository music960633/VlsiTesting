#

CFLAGS = -g 

FILES = tpgmain.o input.o level.o sim.o podem.o test.o init_flist.o faultsim.o display.o tdfsim.o

atpg : $(FILES) 
	gcc $(CFLAGS) $(FILES) -lm -o atpg

tpgmain.o : atpg.h miscell.h tpgmain.c
	gcc $(CFLAGS) -c tpgmain.c
input.o : atpg.h miscell.h
	gcc $(CFLAGS) -c input.c
level.o : atpg.h miscell.h
	gcc $(CFLAGS) -c level.c
sim.o : atpg.h miscell.h logic_tbl.h
	gcc $(CFLAGS) -c sim.c
podem.o : atpg.h miscell.h
	gcc $(CFLAGS) -c podem.c
init_flist.o : atpg.h miscell.h
	gcc $(CFLAGS) -c init_flist.c
faultsim.o : atpg.h miscell.h
	gcc $(CFLAGS) -c faultsim.c
test.o : atpg.h miscell.h
	gcc $(CFLAGS) -c test.c
display.o : atpg.h miscell.h
	gcc $(CFLAGS) -c display.c
tdfsim.o : atpg.h miscell.h
	gcc $(CFLAGS) -c tdfsim.c
clean:
	rm *.o

