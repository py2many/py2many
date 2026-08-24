def for_with_break() raises:
    for i in range(4):
        if i == 2:
            break

        print(i)


def for_with_continue() raises:
    for i in range(4):
        if i == 2:
            continue

        print(i)


def for_with_else() raises:
    var has_break = False
    for i in range(4):
        print(i)
    if has_break != True:
        print("OK")


def while_with_break() raises:
    var i = 0
    while True:
        if i == 2:
            break

        print(i)
        i += 1


def while_with_continue() raises:
    var i = 0
    while i < 5:
        i += 1
        if i == 2:
            continue

        print(i)


def main() raises:
    for_with_break()
    for_with_continue()
    for_with_else()
    while_with_break()
    while_with_continue()
