def func():
    return "aaaa"

class TestClass:
    def func(self):
        return "ssss"

def test():
    var:int = 0
    def innerTest():
        var = 2
        print(var)
    
    innerTest()

if __name__ == "__main__":
    print(func())
    testClass = TestClass()
    print(testClass.func())

    # Function scopes
    test()