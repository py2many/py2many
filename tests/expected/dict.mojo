import testing


fn implicit_keys() -> Bool:
    var CODES = {"KEY": 1}
    return "KEY" in CODES


fn explicit_keys() -> Bool:
    var CODES = {"KEY": 1}
    return "KEY" in CODES.keys()


fn dict_values() -> Bool:
    var CODES = {"KEY": 1}
    return 1 in CODES.values()


fn return_dict_index_str(key: String) -> Int:
    var CODES = {"KEY": 1}
    return CODES[key]


fn return_dict_index_int(key: Int) -> String:
    var CODES = {1: "one"}
    return CODES[key]


fn main() raises:
    testing.assert_true(implicit_keys())
    testing.assert_true(explicit_keys())
    testing.assert_true(dict_values())
    testing.assert_true(return_dict_index_str("KEY") == 1)
    testing.assert_true(return_dict_index_int(1) == "one")
    print("OK")
