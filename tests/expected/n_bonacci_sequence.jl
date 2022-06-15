function bonacciseries(n::Int64, m::Int64)::Vector
    a = repeat([0], m)
    a[n] = 1
    for i = n:m-1
        for j = i-n:i-1
            a[i+1] = a[i+1] + a[j+1]
        end
    end
    return a
end
