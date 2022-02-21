

abstract type AbstractIntListNonEmpty end
abstract type AbstractIntList end
mutable struct IntListNonEmpty <: AbstractIntListNonEmpty
    first::Int64
    rest::IntList
end

function __init__(self::IntListNonEmpty, first::Int64, rest::IntList)
    setfield!(self::IntListNonEmpty, :first, first::Int64)
    setfield!(self::IntListNonEmpty, :rest, rest::IntList)

end

function __repr__(self::IntListNonEmpty)::String
    return IntListNonEmpty(
        getfield!(self::IntListNonEmpty, first::Int64),
        getfield!(self::IntListNonEmpty, rest::IntList),
    )
end
function __eq__(self::IntListNonEmpty, other::IntListNonEmpty)::Bool
    return __key(self) == __key(other)
end

function __key(self::IntListNonEmpty)
    (
        getfield!(self::IntListNonEmpty, first::Int64),
        getfield!(self::IntListNonEmpty, rest::IntList),
    )
end


struct IntList <: AbstractIntList
    NONE::None
    REST::IntListNonEmpty
end

