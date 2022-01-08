
def multiply_list(elems):
    new_elems = []
    for e in elems:
        new_elems.append(e*2)
    return new_elems

if __name__ == "__main__":
    a = list()

    # Append
    a.append("test")
    assert a == ["test"]

    # Clear
    a.clear()
    assert a == []
    assert len(a) == 0

    # Remove
    a.append("test1")
    a.append("test2")
    a.remove("test1")
    assert a == ["test2"]
    assert len(a) == 1
    a.clear() # reset list

    # Copy
    a.append("test")
    b = a.copy()
    assert b == a
    a.clear() # reset list

    # Count
    a.append("test2")
    a.append("test2")
    a.remove("test2")
    assert a.count("test2") == 1
    a.clear() # reset list

    # Extend
    a.append("test1")
    a.extend(b)
    assert a == ["test1", "test"]
    a.clear() # reset list

    # Limitation
    elems = ["1", "2", "3"]
    new_elems = multiply_list(elems)
    assert new_elems == ["11", "22", "33"]

    print("OK")

    # Index
    # a.append("test")
    # assert a.index("test") == 0 # Problems

