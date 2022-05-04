# @jl_class # For PyJL
class Foo:
    def bar(self):
        return self.baz()

    def baz(self) -> int:
        return 10

    def bar_str(self):
        return "a"

# @jl_class # For PyJL
class Person:
    def __init__(self, name:str):
        self.name = name

    def get_name(self):
        return self.name

# @jl_class # For PyJL
class Student(Person):
    def __init__(self, 
                 name:str, 
                 student_number:int, 
                 domain:str = "school.student.pt"):
        self.name = name
        self.student_number = student_number

    def get_name(self):
        return f"{self.name} - {self.student_number}"

class Student2(Person):
    def __init__(self, 
                 name:str, 
                 student_number:int,
                 domain:str = "school.student.pt"):
        if student_number < 0:
            raise ValueError("Student number must be a positive number")
        self.student_number = student_number
        self.name = name

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
    assert s.get_name() == "S - 111111"

    s2 = Student2("S2", 123)
    # Student2("S2", -1) # Should raise an exception
    
    print("OK")
