function show()::Vector
    s = []
    try
        throw(Exception("foo"))
    catch exn
        let e = exn
            if e isa Exception
                push!(s, "foo")
            end
        end
    finally
        push!(s, "Finally")
    end
    try
        3 / 0
    catch exn
        if exn isa ZeroDivisionError
            push!(s, "ZeroDivisionError")
        end
    end
    try
        throw(Exception("foo"))
    catch exn
        push!(s, "foo_2")
    end
    return s
end

function main()
    @assert(show() == ["foo", "Finally", "ZeroDivisionError", "foo_2"])
end

main()
