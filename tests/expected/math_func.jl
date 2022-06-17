function main()
    a = 2^4
    println(join([a], " "))
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
