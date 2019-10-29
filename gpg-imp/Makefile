
#------ MAKE CHANGES TO BASE_DIR : Please put the path to base directory of your pristine gcc-4.7.2 build -----------#
BASE_DIR=`pwd`/../gcc472
#BASE_DIR = /home/pritam/GCC_BUILDS/gcc_4.7.2/gcc-build

INSTALL = $(BASE_DIR)/install
CC = $(INSTALL)/bin/g++


#----- MAKE CHANGES TO TEST : Add the name of your test file with extension .o (say test as test.o) --------#
#------------------------------- Multiple dependent files maybe also be added ------------------------------#
TEST = coalesce.o

#TEST = types-struct.o
#TEST = blocking2.o
#TEST = fp.o
#TEST = struct-heap.o
#TEST = test8.o
#TEST = test34.o
#TEST = loop.o
#TEST = rcfg.o
#TEST = recur.o
#TEST = scc.o
#TEST = coalescing.o
#TEST = ptr-arith.o
#TEST = fp.o

GCCPLUGINS_DIR:= $(shell $(CC) -print-file-name=plugin)
INCLUDE= -I$(GCCPLUGINS_DIR)/include 

FLAGS= -fPIC -g -O0 -fipa-pta -flto -flto-partition=none -DPROFILE 

Profile.o: Profile.cpp Profile.h
	$(CC) $(FLAGS) $(INCLUDE) -c Profile.cpp

IndirectionList.o: IndirectionList.cc IndirectionList.h
	 $(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c IndirectionList.cc

#IndirectionListMap.o: IndirectionListMap.cc IndirectionListMap.h
#	 $(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c IndirectionListMap.cc

fp_prototype.o: fp_prototype.cpp fp_prototype.hpp
	 $(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c fp_prototype.cpp

GPU.o: GPU.cc GPU.h
	 $(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c GPU.cc

GPB.o: GPB.cc GPB.h
	 $(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c GPB.cc

GPG.o: GPG.cc GPG.h
	 $(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c GPG.cc

con.o: con.cpp con.hpp
	 $(CC) $(FLAGS) $(INCLUDE) -c con.cpp

basic_block.o: basic_block.cpp basic_block.hpp
	$(CC) $(FLAGS) $(INCLUDE) -c basic_block.cpp

CoalescingAbstraction.o: CoalescingAbstraction.cc CoalescingAbstraction.h
	 $(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c CoalescingAbstraction.cc

#preprocess.o: preprocess.cpp preprocess.hpp
#	$(CC) $(FLAGS) $(INCLUDE) -c preprocess.cpp

cgraph_node.o: cgraph_node.cpp cgraph_node.hpp
	$(CC) $(FLAGS) $(INCLUDE) -c cgraph_node.cpp	

interval.o: interval.cpp interval.hpp
	 $(CC) $(FLAGS) $(INCLUDE) -c interval.cpp

parser.o: parser.cpp parser.hpp
	$(CC) $(FLAGS) $(INCLUDE) -c parser.cpp	

pointsto.o: pointsto.cc
	$(CC) $(FLAGS) -std=c++11 $(INCLUDE) -c pointsto.cc

%.o : %.c
	$(CC) $(FLAGS) $(INCLUDE) -c $< 

%.o : %.cpp
	$(CC) $(FLAGS) $(INCLUDE) -c $< 

plugin.so: pointsto.o parser.o basic_block.o con.o cgraph_node.o interval.o IndirectionList.o GPU.o GPB.o GPG.o CoalescingAbstraction.o Profile.o fp_prototype.o
	$(CC) $(INCLUDE) $(FLAGS) -shared $^ -o $@

run:  $(TEST) plugin.so
	$(CC) -o result -DPROFILE -fipa-pta -g -flto -flto-partition=none -fplugin=./plugin.so $(TEST) -O3 -fdump-ipa-all

	

clean:
	\rm -f plugin.so *~ *.o a.out result* *.cpp.* *.dot
