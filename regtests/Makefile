SHELL := /bin/bash
test: main
	./main
main: main.cpp
	clang++ -Wall -std=c++14 -I../py14/runtime -o main main.cpp
main.cpp:
	./../transpile_regtests.py
clean:
	rm main
	rm *.cpp
	rm *.hpp
