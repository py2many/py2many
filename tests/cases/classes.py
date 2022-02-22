
class Foo:
    def bar(self):
        return self.baz()

    def baz(self) -> int:
        return 10

    def bar_str(self):
        return "a"

class Person:
    def __init__(self, name:str):
        self.name = name

    def get_name(self):
        return self.name

class Student(Person):
    def __init__(self, name:str, student_number:int):
        # super().__init__(name) # Currenlty unsupported
        self.name = name
        self.student_number = student_number

    def get_name(self):
        return f"{self.student_number} - {self.name}"

if __name__ == "__main__":
    # Accessing class values
    f = Foo()
    b = f.bar()
    assert b == 10
    c = f.bar_str()
    assert c == "a"

    #  Test inheritance
    p = Person("P")
    s = Student("S", 111111)
    assert p.get_name() == "P"
    assert s.get_name() == "111111 - S"
    
    print("OK")
