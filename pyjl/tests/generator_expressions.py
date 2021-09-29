

if __name__ == "__main__":
    value = " ".join(str(x) for x in range(10) if x > 4 if x < 8) # Works
    # value = " ".join(str(x) + " " + str(y) for x in range(10) if x > 4 for y in range(8)) # Does not Work
    # value = " ".join(str(x + y) for x in range(10) if x > 4 for y in range(8)) # Works
    print(value)

