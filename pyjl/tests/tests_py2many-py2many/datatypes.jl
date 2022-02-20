using DataClass
abstract type AbstractIntListNonEmpty end
abstract type AbstractIntList end


@dataclass mutable struct IntListNonEmpty::AbstractIntListNonEmpty 
first::Int64
rest::IntList
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end

struct IntList::AbstractIntList 
NONE::None
REST::IntListNonEmpty
end

