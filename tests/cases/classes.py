# @jl_class # For PyJL
# Simple class translation
class Foo:
    def bar(self):
        return self.baz()

    def baz(self) -> int:
        return 10

    def bar_str(self):
        return "a"


######################################
### Example of the Diamond Problem ###
######################################

# @jl_class # For PyJL
class Person:
    def __init__(self, name: str):
        self.name = name

    def get_name(self):
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

    def get_name(self):
        return f"{self.name} - {self.student_number}"


class Worker(Person):
    def __init__(
        self, name: str, company_name: str, hours_per_week: int
    ):
        Person.__init__(self, name)
        self.company_name = company_name
        self.hours_per_week = hours_per_week


class StudentWorker(Student, Worker):
    def __init__(self, name: str, student_number: int, domain: str,
            company_name: str, hours_per_week: int, is_exhausted:bool):
        Student.__init__(self, name, student_number, domain)
        Worker.__init__(self, name, company_name, hours_per_week)
        self.is_exhausted = is_exhausted


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

    # Exceptions
    # Student("S2", -1) # Raise an exception if uncommented

    # Multiple inheritance
    sw = StudentWorker("Timo Marcello", 1111, "school.student.pt",
        "Cisco", 40, True)
    assert sw.company_name == "Cisco"
    assert sw.is_exhausted == True
    print("OK")
