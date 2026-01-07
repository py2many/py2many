#!/usr/bin/env python3


def show():
    # Delete from list
    my_list = [1, 2, 3, 4, 5]
    del my_list[2]
    print(len(my_list))

    # Delete from dict
    my_dict = {"a": 1, "b": 2, "c": 3}
    del my_dict["b"]
    print(len(my_dict))


if __name__ == "__main__":
    show()
