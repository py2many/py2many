def for_with_break():
    for i in range(4):
        if i == 2:
            break
        print(i)


def for_with_continue():
    for i in range(4):
        if i == 2:
            continue
        print(i)


def for_with_else():
    for i in range(4):
        print(i)
    else:
        print("OK")


def while_with_break():
    i = 0
    while True:
        if i == 2:
            break
        print(i)
        i += 1


def while_with_continue():
    i = 0
    while i < 5:
        i += 1
        if i == 2:
            continue
        print(i)


if __name__ == "__main__":
    for_with_break()
    for_with_continue()
    # https://github.com/adsharma/py2many/issues/415
    for_with_else()
    while_with_break()
    while_with_continue()
