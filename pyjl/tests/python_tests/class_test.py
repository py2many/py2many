class Person:
    def __init__(self, name:str):
        self.name = name

    def get_name(self) -> str:
        return self.name

class Student(Person):
    def __init__(self, name:str, student_number:int):
        super().__init__(name)
        self.student_number = student_number

    def get_name(self) -> str:
        return f"{self.student_number} - {self.name}"

if __name__ == "__main__":
    p = Person("person")
    print(p.get_name())
    s = Student("student", 12345)
    print(s.get_name())