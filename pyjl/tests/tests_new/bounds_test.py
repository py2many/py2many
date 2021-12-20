if __name__ == "__main__":
    seq: list = [1,2,3,4,5] 
    seq_copy: list = [1,2,3,4,5]
    gap = 1
    for i in range(len(seq) - gap):
        # Assert that the list has not changed
        assert seq[i] == seq_copy[i]
    
    # Test limit access
    assert seq[0] == 1 # First value
    assert seq[2] == 3 # Some value in the middle
    assert seq[-1] == 5 # Last Value