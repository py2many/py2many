if __name__ == "__main__":
    value = " ".join(str(x) for x in range(10) if x > 4 if x < 8)
    assert value == "5 6 7"

    value2 = " ".join(
        str(x) + " " + str(y) for x in range(5) if x > 1 for y in range(2)
    )
    assert value2 == "2 0 2 1 3 0 3 1 4 0 4 1"

    value3 = " ".join(str(x + y) for x in range(5) if x > 1 for y in range(4))
    assert value3 == "2 3 4 5 3 4 5 6 4 5 6 7"
