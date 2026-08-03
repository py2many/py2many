function show()
    try
        3 / 0
    catch exn
        if exn isa ZeroDivisionError
            println(join(["ZeroDivisionError"], " "))
        end
    end
end

function main()
    show()
end

main()
