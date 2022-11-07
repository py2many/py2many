def lenient_test_1():
    x = 2
    x = "2"
    l = ["1"]
    l.append(2)

def lenient_test_2():
    # From https://google.github.io/pytype/
    lst = ["PyCon"]
    lst.append(2019)
    return [str(x) for x in lst]

if __name__ == "__main__":
    lenient_test_1()
    lst = lenient_test_2()
    assert lst == ["PyCon", "2019"]