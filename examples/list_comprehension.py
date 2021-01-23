def main():
    initial = [1, 2, 3]
    transformed = [x * 2 for x in initial]
    if 4 in transformed:
        print("Four exists")

    if 5 not in transformed:
        print("Five does not")
