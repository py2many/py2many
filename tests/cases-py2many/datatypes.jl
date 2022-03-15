
abstract type AbstractIntListNonEmpty end
abstract type AbstractIntList end

mutable struct IntListNonEmpty <: AbstractIntListNonEmpty

end

                function __init__(self::AbstractIntListNonEmpty, )
                    setfield!(self::AbstractIntListNonEmpty, :, )
                end
            

                function __repr__(self::AbstractIntListNonEmpty)::String 
                    return AbstractIntListNonEmpty(self.) 
                end
            

                function __eq__(self::AbstractIntListNonEmpty, other::AbstractIntListNonEmpty)::Bool
                    return __key(self) == __key(other)
                end
            

                function __key(self::AbstractIntListNonEmpty)
                    (self.)
                end
                
mutable struct IntList <: AbstractIntList

end

