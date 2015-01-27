CPPFLAGS = -Wall -std=c++14 -I../py14/runtime 
test: main
	./main
main: main.cpp
	$(CXX) $(CPPFLAGS) -o main main.cpp
main.cpp:
	./../transpile_regtests.py
clean:
	rm main
	rm *.cpp
	rm *.hpp
