#!/usr/bin/env python3

if __name__ == "__main__":
    a = 10
    b = "test"
    c = 2 + 4

    str1 = f"hello {a+1} world"
    assert str1 == "hello 11 world"

    str2 = f"hello {b} world {a}"
    assert str2 == "hello test world 10"

    str3 = f"hello {b} world {a} test {c}"
    assert str3 == "hello test world 10 test 6"

    a = 10
    assert f"hello {a+1} world" == "hello 11 world"
    assert f"test {a+1} test {a+20} test {a+30}" == "test 11 test 30 test 40" 
    
    print("OK")
