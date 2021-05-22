def implicit_keys():
    CODES = {"KEY": 1}
    return "KEY" in CODES


def explicit_keys():
    CODES = {"KEY": 1}
    return "KEY" in CODES.keys()


def dict_values():
    CODES = {"KEY": 1}
    return 1 in CODES.values()


if __name__ == "__main__":
    assert implicit_keys()
    assert explicit_keys()
    assert dict_values()
    print("OK")
