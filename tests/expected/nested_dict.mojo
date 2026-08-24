def nested_containers() raises -> Bool:
    var CODES = {"KEY": List([1, 3])}
    return 1 in CODES["KEY"]


def main() raises:
    if nested_containers():
        print("OK")
