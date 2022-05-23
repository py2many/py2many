function test()
    if (i = 2) < 3
        @assert(i == 2)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    test()
end
