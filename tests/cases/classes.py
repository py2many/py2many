# Simple class translation

class Foo:
    def bar(self):
        return self.baz()

    def baz(self) -> int:
        return 10

    def bar_str(self):
        return "a"

class Shape():
    def __init__(self, x, y):
        # Center on a 2-dimensional plane
        self.x = x
        self.y = y

    def position(self):
        return f"({self.x}, {self.y})"
    
class Square(Shape):
    """Two-dimensional square"""
    def __init__(self, x, y, side):
        super().__init__(x, y)
        self.side = side

    def area(self):
        self.x * self.y


######################################
### Example of the Diamond Problem ###
######################################

# @jl_class # For PyJL
class Person:
    def __init__(self, name: str):
        self.name = name

    def get_id(self):
        return self.name


# @jl_class # For PyJL
class Student(Person):
    def __init__(
        self, name: str, student_number: int, domain: str = "school.student.pt"
    ):
        if student_number < 0:
            raise ValueError("Student number must be a positive number")
        self.name = name
        self.student_number = student_number
        self.domain = domain

    def get_id(self):
        return f"{self.name} - {self.student_number}"

# @jl_class # For PyJL
class Worker(Person):
    def __init__(
        self, name: str, company_name: str, hours_per_week: int
    ):
        self.name = name
        self.company_name = company_name
        self.hours_per_week = hours_per_week


class StudentWorker(Student, Worker):
    def __init__(self, name: str, student_number: int, domain: str,
            company_name: str, hours_per_week: int, is_exhausted:bool):
        Student.__init__(self, name, student_number, domain)
        Worker.__init__(self, name, company_name, hours_per_week)
        self.is_exhausted = is_exhausted


if __name__ == "__main__":
    # Accessing class values and methods
    f = Foo()
    b = f.bar()
    assert b == 10
    c = f.bar_str()
    assert c == "a"

    shape = Shape(1, 3)
    square = Square(2, 4, 5)
    assert square.position() == "(2, 4)"

    # Test inheritance
    p = Person("P")
    assert p.name == "P"
    assert p.get_id() == "P"

    s = Student("S", 111111)
    assert s.name == "S"
    assert s.student_number == 111111
    assert s.domain == "school.student.pt"
    assert s.get_id() == "S - 111111"

    w = Worker("John", "Siemens", 35)
    assert w.name == "John"
    assert w.company_name == "Siemens"
    assert w.hours_per_week == 35
    assert w.get_id() == "John"

    # Exceptions
    # Student("S2", -1) # Raises an exception if uncommented

    # Multiple inheritance
    sw = StudentWorker("Timo Marcello", 1111, "school.student.pt",
        "Cisco", 40, True)
    assert sw.company_name == "Cisco"
    assert sw.is_exhausted == True
    assert sw.name == "Timo Marcello"
    assert sw.student_number == 1111
    assert sw.domain == "school.student.pt"
    assert sw.company_name == "Cisco"
    assert sw.hours_per_week == 40
    assert sw.is_exhausted == True
    print("OK")
