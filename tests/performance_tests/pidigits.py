# The Computer Language Benchmarks Game
# https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
#
# Translated from Mr Ledrug's C program by Jeremy Zerfas.
#
# WARNING: I normally do my programming in other languages. This may not be an
# optimal Python program. Please contribute a better program if you can make a
# better program.

from ctypes import c_int, c_ulong, c_void_p, byref, CDLL, Structure
from ctypes.util import find_library
from sys import argv


# We'll be using GMP for our arbitrary-precision math needs instead of using
# Python's built in arbitrary-precision math because it is significantly faster.
GMP=CDLL(find_library("gmp"))

# By default, Python assumes that C functions will return int's but that is not
# quite correct for the __gmpz_get_ui() function which returns an unsigned long
# instead so we tell it the correct type here.
GMP.__gmpz_get_ui.restype=c_ulong


class mpz_t(Structure):
    _fields_=[("mp_alloc", c_int),
              ("mp_size", c_int),
              ("mp_d", c_void_p)]

tmp1=mpz_t()
tmp2=mpz_t()
acc=mpz_t()
den=mpz_t()
num=mpz_t()


def extract_Digit(nth):
    # Joggling between tmp1 and tmp2, so GMP won't have to use temp buffers.
    GMP.__gmpz_mul_ui(byref(tmp1), byref(num), c_ulong(nth))
    GMP.__gmpz_add(byref(tmp2), byref(tmp1), byref(acc))
    GMP.__gmpz_tdiv_q(byref(tmp1), byref(tmp2), byref(den))

    return GMP.__gmpz_get_ui(byref(tmp1))


def eliminate_Digit(d):
    GMP.__gmpz_submul_ui(byref(acc), byref(den), c_ulong(d))
    GMP.__gmpz_mul_ui(byref(acc), byref(acc), c_ulong(10))
    GMP.__gmpz_mul_ui(byref(num), byref(num), c_ulong(10))


def next_Term(k):
    k2=k*2+1
    GMP.__gmpz_addmul_ui(byref(acc), byref(num), c_ulong(2))
    GMP.__gmpz_mul_ui(byref(acc), byref(acc), c_ulong(k2))
    GMP.__gmpz_mul_ui(byref(den), byref(den), c_ulong(k2))
    GMP.__gmpz_mul_ui(byref(num), byref(num), c_ulong(k))


def main():
    n=int(argv[1])

    GMP.__gmpz_init_set_ui(byref(tmp1), c_ulong(0))
    GMP.__gmpz_init_set_ui(byref(tmp2), c_ulong(0))

    GMP.__gmpz_init_set_ui(byref(acc), c_ulong(0))
    GMP.__gmpz_init_set_ui(byref(den), c_ulong(1))
    GMP.__gmpz_init_set_ui(byref(num), c_ulong(1))


    i=0
    k=0
    while i<n:
        k+=1
        next_Term(k)
        if GMP.__gmpz_cmp(byref(num), byref(acc))>0:
            continue


        d=extract_Digit(3)
        if d!=extract_Digit(4):
            continue


        print(chr(48+d), end="")
        i+=1
        if i%10==0:
            print("\t:%d" % (i))
        eliminate_Digit(d)


main()