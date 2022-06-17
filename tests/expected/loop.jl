function for_with_break()
    for i in (0:4-1)
        if i == 2
            break
        end
        println(join([i], " "))
    end
end

function for_with_continue()
    for i in (0:4-1)
        if i == 2
            continue
        end
        println(join([i], " "))
    end
end

function for_with_else()
    for i in (0:4-1)
        println(join([i], " "))
    end
end

function while_with_break()
    i = 0
    while true
        if i == 2
            break
        end
        println(join([i], " "))
        i += 1
    end
end

function while_with_continue()
    i = 0
    while i < 5
        i += 1
        if i == 2
            continue
        end
        println(join([i], " "))
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    for_with_break()
    for_with_continue()
    while_with_break()
    while_with_continue()
end
