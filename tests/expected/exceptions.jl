function show()
    try
        throw(Exception("foo"))
    catch exn
        let e = exn
            if e isa Exception
                println(join(["caught"], " "))
            end
        end
    finally
        println(join(["Finally"], " "))
    end
    try
        throw(Exception("foo"))
    catch exn
        println(join(["Got it"], " "))
    end
    try
        throw(Exception("foo"))
    catch exn
        let e = exn
            if e isa Exception
                @assert(findfirst("foo", string(e)) != Nothing)
            end
        end
    end
end

function main()
    show()
end

main()
