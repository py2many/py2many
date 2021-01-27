
struct Rectangle
    height::Int64
    length::Int64
end

function is_square(self::Rectangle)::Bool
    return self.height == self.length
end
