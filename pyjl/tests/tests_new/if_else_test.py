def something():
    print("Something")

def lookup_and_write(values, start, stop):
    if isinstance(values, bytearray):
        output = values
    elif 1 == 2:
        print("Never reach")
    elif 2 == 1:
        print("Never reach")
    elif 3 == 1:
        print("Never reach")
    else:
        output = bytearray()
        output[:stop - start] = something()

if __name__ == "__main__":
    lookup_and_write([1,2], 0, 1)