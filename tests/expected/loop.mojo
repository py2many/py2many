fn for_with_break():
    for i in range(4):
        if i == 2:
            break

        print(i)


fn for_with_continue():
    for i in range(4):
        if i == 2:
            continue

        print(i)


fn for_with_else():
    var has_break = False
    for i in range(4):
        print(i)
    if has_break != True:
        print("OK")


fn while_with_break():
    var i = 0
    while True:
        if i == 2:
            break

        print(i)
        i += 1


fn while_with_continue():
    var i = 0
    while i < 5:
        i += 1
        if i == 2:
            continue

        print(i)


fn main():
    for_with_break()
    for_with_continue()
    for_with_else()
    while_with_break()
    while_with_continue()
