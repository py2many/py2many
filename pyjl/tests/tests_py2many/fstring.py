#!/usr/bin/env python3

if __name__ == "__main__":
    a = 10
    assert f"hello {a+1} world" == "hello 11 world"
    assert f"test {a+1} test {a+20} test {a+30}" == "test 11 test 30 test 40" 
    print("OK")
