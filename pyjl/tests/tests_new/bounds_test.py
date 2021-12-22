if __name__ == "__main__":
    seq: list = [1,2,3,4,5] 
    seq_copy: list = [1,2,3,4,5]
    gap = 1
    for i in range(len(seq) - gap):
        # Assert that the list has not changed
        assert seq[i] == seq_copy[i]

    complex_list = [([1,2],3,4)]
    for ([a1,a2], b, c) in complex_list:
        assert a1 == 1
        assert a2 == 2
        assert b == 3
        assert c == 4

        # Nested Loop test
        arr = []
        a = 1
        for j in range(0,2):
            arr.append(a)
            a += 1
        
        assert arr[0] == 1
        assert arr[1] == 2
    
    # Test limit access
    assert seq[0] == 1 # First value
    assert seq[2] == 3 # Some value in the middle
    assert seq[-1] == 5 # Last Value
    
    x = 1
    assert seq[x] == 2

    print("OK")