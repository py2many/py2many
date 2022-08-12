function find_factors(n)
    for i = 2:n-1
        has_break = false
        for j = 2:i-1
            if (i % j) == 0
                println("$(i) equals $(j) * $(i / j)")
                has_break = true
                break
            end
        end
        if has_break != true
            println("$(i) is a prime number")
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    find_factors(100)
end
