
abstract type AbstractIntListNonEmpty end
abstract type AbstractIntList end
mutable struct IntListNonEmpty <: AbstractIntListNonEmpty
    first::Int64
    rest::AbstractIntList
end

function __repr__(self::AbstractIntListNonEmpty)::String
    return AbstractIntListNonEmpty(self.first, self.rest)
end

function __eq__(self::AbstractIntListNonEmpty, other::AbstractIntListNonEmpty)::Bool
    return __key(self) == __key(other)
end

function __key(self::AbstractIntListNonEmpty)
    (self.first, __key(self.rest))
end

mutable struct IntList <: AbstractIntList
    NONE
    REST::AbstractIntListNonEmpty
end
