function show()
    try
        raise!(Exception("foo")) # unsupported
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
        raise!(Exception("foo")) # unsupported
    catch exn
        println(join(["Got it"], " "))
    end
end

function main()
    show()
end

main()
