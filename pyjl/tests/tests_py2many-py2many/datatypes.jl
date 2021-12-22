using DataClass


@dataclass mutable struct IntListNonEmpty
first::Int64
rest::IntList
_initvars = [_init=true, _repr=true, _eq=true, _order=false, _unsafe_hash=false, _frozen=false]
end

struct IntList
NONE::None
REST::IntListNonEmpty
end

