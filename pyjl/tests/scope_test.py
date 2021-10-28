def func():
    return "aaaa"

class TestClass:
    def func(self):
        return "ssss"

if __name__ == "__main__":
    print(func())
    testClass = TestClass()
    print(testClass.func())