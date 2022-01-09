class Foo:
    def bar(self):
        return self.baz()

    def baz(self) -> int:
        return 10

# class Bag:
#     def __init__(self):
#         self.data = []

#     def add(self, x):
#         self.data.append(x)

#     def addtwice(self, x):
#         self.add(x)
#         self.add(x)

class Person:
    def __init__(self, name:str):
        self.name = name

    def get_name(self):
        return self.name

class Student(Person):
    def __init__(self, name:str, student_number:int):
        super().__init__(name)
        self.student_number = student_number

    def get_name(self):
        return f"{self.student_number} - {self.name}"

if __name__ == "__main__":
    f = Foo()
    b = f.bar()
    assert b == 10

    #  Test inheritance
    p = Person("Michael Carmichael")
    s = Student("Michael Carmichael", 111111)
    assert p.get_name() == "Michael Carmichael"
    assert s.get_name() == "111111 - Michael Carmichael"

    print("OK")
