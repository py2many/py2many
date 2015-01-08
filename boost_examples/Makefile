BOOST_LIB = /usr/lib
TARGET = extern_functions
CXX = clang++
PYTHON_INCLUDE = /usr/include/python$(PYTHON_VERSION)
BOOST_INC = /usr/include/boost
PYTHON_VERSION = 2.7
$(TARGET).so: $(TARGET).o
	$(CXX) -std=c++14 -shared -Wl,--export-dynamic $(TARGET).o -L$(BOOST_LIB) -lboost_python -L/usr/lib/python$(PYTHON_VERSION)/config -lpython$(PYTHON_VERSION) -O3 -o $(TARGET).so
$(TARGET).o: $(TARGET).cpp
	$(CXX) -std=c++14 -I$(PYTHON_INCLUDE) -I$(BOOST_INC) -fPIC -c $(TARGET).cpp
clean:
	rm -f *.o *.so
