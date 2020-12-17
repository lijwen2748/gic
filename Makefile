CSOURCES = aiger.c picosat/picosat.c

CPPSOURCES = gic.cpp satsolver.cpp mainsolver.cpp invsolver.cpp model.cpp utility.cpp data_structure.cpp main.cpp \
	minisat/core/Solver.cc minisat/utils/Options.cc minisat/utils/System.cc
#CSOURCES = aiger.c picosat/picosat.c
#CPPSOURCES = bfschecker.cpp checker.cpp carsolver.cpp mainsolver.cpp model.cpp utility.cpp data_structure.cpp main.cpp \
	glucose/core/Solver.cc glucose/utils/Options.cc glucose/utils/System.cc

OBJS = gic.o satsolver.o mainsolver.o invsolver.o model.o main.o utility.o data_structure.o aiger.o\
	Solver.o Options.o System.o picosat.o

CFLAG = -I../ -I./minisat -D__STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -c -g -fpermissive
#CFLAG = -I../ -I./glucose -D__STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -c -g 

LFLAG = -g -lz -lpthread 

GCC = gcc

GXX = g++

simplegic: $(CSOURCES) $(CPPSOURCES)
	$(GCC) $(CFLAG) $(CSOURCES)
	$(GCC) $(CFLAG) -std=c++11 $(CPPSOURCES)
	$(GXX) -o simplegic $(OBJS) $(LFLAG)
	rm *.o

picosat: $(CSOURCES) $(CPPSOURCES)
	$(GCC) $(CFLAG) $(CSOURCES)
	$(GCC) $(CFLAG) -D ENABLE_PICOSAT -std=c++11 $(CPPSOURCES)
	$(GXX) -o simplegic $(OBJS) $(LFLAG)
	rm *.o


clean: 
	rm simplegic
	
.PHONY: simplegic
