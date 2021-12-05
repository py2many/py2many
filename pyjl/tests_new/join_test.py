
class Hello:
    def why(self):
        return "ola"

if __name__ == "__main__":
    # a = "a"
    # b = "ab"
    # print(a.join(b))

    # tuple = ("One", "Two", "Three")
    # value_str = " ".join(tuple)
    # print(value_str)

    # tuple_2 = ["The", "challenge", "is", "on"]
    # value_str_2 = "#".join(["The", "challenge", "is", "on"])
    # print(value_str_2)

    print(" ".join([Hello().why(), "adeus"]))


