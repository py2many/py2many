def func():
    return "test"

class TestClass:
    def func(self):
        return "test2"

def test():
    num:int = 2
    teststr:str = "test"
    def inner_test():
        return num*teststr
    
    def inner_test_2():
        num = 4
        # num: int = 4 # fails with annotation (pyjl)
        return num*teststr
    
    assert inner_test() == "testtest"
    assert inner_test_2() == "testtesttesttest"

if __name__ == "__main__":
    assert func() == "test"
    testClass = TestClass()

    assert testClass.func() == "test2"

    # Function scopes
    test()