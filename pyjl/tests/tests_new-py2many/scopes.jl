function main()
    x = 1
    function myfun()::Int64
    return x
    end

    x = 10
    println(myfun());
end

main()
