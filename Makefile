CXX=clang++
#CXXFLAGS=`llvm-config-3.5 --cxxflags all`
#LIBS=`llvm-config-3.5 --libs all`
LIBS= -rdynamic `llvm-config-3.5 --ldflags --system-libs --libs all` -lstdc++ ../marpa-cpp-rules/libmarpa.a
CXXFLAGS=`llvm-config-3.5 --cxxflags` -g -O0 

#all: test2
	#./test2

all: toy2 test2.toy
	./toy2 <test2.toy

test: output.o main.o
	$(CXX) -o $@ $^ -lstdc++

test2: output2.o main.o
	$(CXX) -o $@ $^ -lstdc++

toy: toy.o
	$(CXX) -o $@ $^ $(LIBS)

toy2: toy2.o ../marpa-cpp-rules/errors.o
	$(CXX) -o $@ $^ $(LIBS)

toy2.cpp: tree.hpp codegen.hpp
toy2.o: toy2.cpp tree.hpp toy2.hpp codegen.hpp marpa-cpp/marpa.hpp

output.ll: toy test.toy
	./toy <test.toy 2> $@

output2.ll: toy2 test2.toy
	./toy2 <test2.toy > $@

%.o: %.ll
	$(CXX) -c -o $@ $< $(CXXFLAGS)

clean:
	rm -f *.o
	rm -f *.ll
	rm -f toy2 toy test test2

