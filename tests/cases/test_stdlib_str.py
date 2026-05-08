def test_str_methods():
    s = "  Hello World  "
    print(s.lower())
    print(s.upper())
    print(s.capitalize())
    print(s.strip())
    print(s.lstrip())
    print(s.rstrip())

    parts = s.split()
    print(parts)

    joined = "-".join(["a", "b", "c"])
    print(joined)

    print(s.find("World"))
    print(s.replace("World", "Vlang"))

    if "123".isdigit():
        print("digit")
    if "abc".isalpha():
        print("alpha")
    if "   ".isspace():
        print("space")


if __name__ == "__main__":
    test_str_methods()
