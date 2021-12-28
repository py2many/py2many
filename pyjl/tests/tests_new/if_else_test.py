def something():
    return "test"

def lookup_and_write(values):
    output = None
    if len(values) == 1:
         output = values[0]
    elif len(values) == 2:
         output = values[1]
    elif len(values) == 3:
         output = values[2]
    else:
        output = values
        
    return output

def lookup_and_write_without_else(values):
    output = None
    if len(values) == 1:
         output = values[0]
    elif len(values) == 2:
         output = values[1]
    elif len(values) == 3:
         output = values[2]
    return output

if __name__ == "__main__":
    assert lookup_and_write([]) == []
    assert lookup_and_write([1]) == 1
    assert lookup_and_write([1,2]) == 2
    assert lookup_and_write([1,2,3]) == 3
    assert lookup_and_write([1,2,3,4]) == [1,2,3,4]

    assert lookup_and_write_without_else([]) == None
    assert lookup_and_write_without_else([1]) == 1
    assert lookup_and_write_without_else([1,2]) == 2
    assert lookup_and_write_without_else([1,2,3]) == 3
    assert lookup_and_write_without_else([1,2,3,4]) == None

    print("OK")