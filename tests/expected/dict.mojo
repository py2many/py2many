def implicit_keys() raises -> Bool:
    var CODES = {"KEY": 1}
    return "KEY" in CODES


def explicit_keys() raises -> Bool:
    var CODES = {"KEY": 1}
    return "KEY" in CODES


def dict_values() raises -> Bool:
    var CODES = {"KEY": 1}
    for _value in CODES.values():
        if _value == 1:
            return True
    return False


def return_dict_index_str(key: String) raises -> Int:
    var CODES = {"KEY": 1}
    return CODES[key]


def return_dict_index_int(key: Int) raises -> String:
    var CODES = {1: "one"}
    return CODES[key]


def main() raises:
    assert implicit_keys()
    assert explicit_keys()
    assert dict_values()
    assert return_dict_index_str("KEY") == 1
    assert return_dict_index_int(1) == "one"
    print("OK")
