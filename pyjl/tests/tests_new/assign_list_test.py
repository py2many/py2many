
if  __name__ == "__main__":
    [a,b,c] = [1,2,3]
    print(a)
    pairs = [(([2,2,2], 2, 2), ([3,3,3], 3, 3))]
    for (([x1, y1, z1], v1, m1),
             ([x2, y2, z2], v2, m2)) in pairs:
        print(x1)
        print(y1)
        print(z1)
        print(x2)
        print(y2)
        print(z2)
    
