
if __name__ == "__main__":
    l = [1,2,3]
    b = ["a", "b", "c"]
    x = 0
    ll = l[(x + 1):]
    x = 1
    lb = b[(x + 1):]

    assert ll == [2,3]
    assert lb == ["c"]
