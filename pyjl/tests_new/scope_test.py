def func():
    return "aaaa"

class TestClass:
    def func(self):
        return "ssss"

def test():
    num:int = 2
    teststr:str = "ola"
    def inner_test():
        print(num*teststr)
    
    def inner_test_2():
        num: int = 4
        print(num*teststr)
    
    inner_test()
    inner_test_2()

if __name__ == "__main__":
    print(func())
    testClass = TestClass()
    print(testClass.func())

    # Function scopes
    test()