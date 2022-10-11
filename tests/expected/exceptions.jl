function show()
    try
        throw(Exception("foo"))
    catch exn
        let e = exn
            if e isa Exception
                println("caught")
            end
        end
    finally
        println("Finally")
    end
    try
        throw(Exception("foo"))
    catch exn
        println("Got it")
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
