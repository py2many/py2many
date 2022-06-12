from ctypes import c_int16, c_int64, c_uint64

def main():
    a = c_int16(1)
    b = a.value
    print(b)

    c = c_int64(1)
    d = c.value
    print(d)

    e = c_uint64(1)
    f = e.value
    print(f)


if __name__ == "__main__":
    main()
