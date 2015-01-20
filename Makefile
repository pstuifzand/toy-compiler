CXX=clang++
#CXXFLAGS=`llvm-config-3.5 --cxxflags all`
#LIBS=`llvm-config-3.5 --libs all`
LIBS=`llvm-config-3.5 --ldflags --system-libs --libs core engine` -lstdc++
CXXFLAGS=-g `llvm-config-3.5 --cxxflags --libs core engine`

all: test2
	./test2

test: output.o main.o
	$(CXX) -o $@ $^ -lstdc++

test2: output2.o main.o
	$(CXX) -o $@ $^ -lstdc++

toy: toy.o
	$(CXX) -o $@ $^ $(LIBS)

toy2: toy2.o
	$(CXX) -o $@ $^ $(LIBS)

toy2.cpp: tree.hpp

output.ll: toy test.toy
	./toy <test.toy 2> $@

output2.ll: toy2 test.toy
	./toy2 <test.toy 2> $@

%.o: %.ll
	$(CXX) -c -o $@ $< $(CXXFLAGS)

clean:
	rm -f *.o
	rm -f toy2 toy test test2

