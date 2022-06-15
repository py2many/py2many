if __name__ == "__main__":
    l = [1, 2, 3]
    b = ["a", "b", "c"]
    x = 0
    assert l[(x + 1) :] == [2, 3]

    x = 1
    assert b[(x + 1) :] == ["c"]

    output = [1, 2, 3, 4, 5, 6]
    start = 1
    stop = 3
    assert output[: stop - start] == [1, 2]

    # Testing with last element
    assert output[-1:] == [6]
    assert output[-1] == 6

    print("OK")
