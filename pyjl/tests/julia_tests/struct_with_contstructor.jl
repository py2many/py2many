struct mpz_t <: Structure
    _fields_::Vector = [("mp_alloc", c_int), ("mp_size", c_int), ("mp_d", c_void_p)]
    function mpz_t(;kwargs...)
        K = new()
        for (key, value) in kwargs
            setfield!(K, key, value)
        end
        return K
    end
end