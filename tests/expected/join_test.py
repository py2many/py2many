class Hello:
    def test(self):
        return "ola"


if __name__ == "__main__":
    # Test 1
    a = "a"
    b = "ab"
    assert a.join(b) == "aab"
    # Test 2
    tuple = ("One", "Two", "Three")
    value_str = " ".join(tuple)
    assert value_str == "One Two Three"
    # Test 3
    tuple_2 = ["The", "challenge", "is", "on"]
    value_str_2 = "#".join(["The", "challenge", "is", "on"])
    assert value_str_2 == "The#challenge#is#on"
    # Test 4
    assert " ".join([Hello().test(), "adeus"]) == "ola adeus"
    # Test 5
    assert "\n".join([Hello().test(), "adeus"]) == "ola\nadeus"

    # All Tests pass
    print("OK")
