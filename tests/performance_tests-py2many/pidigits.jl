using Printf

using ctypes.util: find_library

abstract type Abstractmpz_t <: AbstractStructure end
GMP = CDLL(find_library("gmp"))
restype(GMP.__gmpz_get_ui) = c_ulong
mutable struct mpz_t <: Abstractmpz_t
    _fields_::Vector{Tuple}

    mpz_t(
        _fields_::Vector{Tuple} = [
            ("mp_alloc", c_int),
            ("mp_size", c_int),
            ("mp_d", c_void_p),
        ],
    ) = new(_fields_)
end

tmp1 = mpz_t()
tmp2 = mpz_t()
acc = mpz_t()
den = mpz_t()
num = mpz_t()
function extract_Digit(nth)
    __gmpz_mul_ui(GMP, byref(tmp1), byref(num), c_ulong(nth))
    __gmpz_add(GMP, byref(tmp2), byref(tmp1), byref(acc))
    __gmpz_tdiv_q(GMP, byref(tmp1), byref(tmp2), byref(den))
    return __gmpz_get_ui(GMP, byref(tmp1))
end

function eliminate_Digit(d)
    __gmpz_submul_ui(GMP, byref(acc), byref(den), c_ulong(d))
    __gmpz_mul_ui(GMP, byref(acc), byref(acc), c_ulong(10))
    __gmpz_mul_ui(GMP, byref(num), byref(num), c_ulong(10))
end

function next_Term(k)
    k2 = k * 2 + 1
    __gmpz_addmul_ui(GMP, byref(acc), byref(num), c_ulong(2))
    __gmpz_mul_ui(GMP, byref(acc), byref(acc), c_ulong(k2))
    __gmpz_mul_ui(GMP, byref(den), byref(den), c_ulong(k2))
    __gmpz_mul_ui(GMP, byref(num), byref(num), c_ulong(k))
end

function main()
    n = parse(Int, argv[2])
    __gmpz_init_set_ui(GMP, byref(tmp1), c_ulong(0))
    __gmpz_init_set_ui(GMP, byref(tmp2), c_ulong(0))
    __gmpz_init_set_ui(GMP, byref(acc), c_ulong(0))
    __gmpz_init_set_ui(GMP, byref(den), c_ulong(1))
    __gmpz_init_set_ui(GMP, byref(num), c_ulong(1))
    i = 0
    k = 0
    while i < n
        k += 1
        next_Term(k)
        if __gmpz_cmp(GMP, byref(num), byref(acc)) > 0
            continue
        end
        d = extract_Digit(3)
        if d != extract_Digit(4)
            continue
        end
        println(chr(48 + d), "")
        i += 1
        if (i % 10) == 0
            @printf("\t:%d", i)
        end
        eliminate_Digit(d)
    end
end

main()
