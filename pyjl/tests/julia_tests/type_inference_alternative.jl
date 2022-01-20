function sum_two(x, y)
    if isa(x, Int64) && isa(y, Int64)
        return x + y
    elseif isa(x, Vector) && isa(y, Vector)
        return [x;y] 
    end
end

test(1,2)
test([1], [2])