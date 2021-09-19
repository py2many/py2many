import Base: +, -, *, &, |, xor, ==, ~

for op in (:+, :-, :&, :|, :xor, :(==))
    @eval begin
        function ($op)(a::Pyenum{T}, b::Pyenum{S}) where {T<:Any,S<:Any}
            N = promote_type(T, S)
            ($op)(N(a), N(b))
        end
        function ($op)(a::Pyenum{T}, b::S) where {T<:Any,S<:Any}
            N = promote_type(T, S)
            ($op)(N(a), N(b))
        end
        function ($op)(a::T, b::Pyenum{S}) where {T<:Any,S<:Any}
            N = promote_type(T, S)
            ($op)(N(a), N(b))
        end
    end
end

function ~(a::Pyenum{T}) where {T<:Any}
    ~(T(a))
end

Base.convert(::Type{T1}, x::Pyenum{T2}) where {T1<:Any,T2<:Any} = convert(T1, T2(x))
