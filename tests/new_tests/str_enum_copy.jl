using SuperEnum

@se Colors begin
    RED => "red"
    GREEN => "green"
    BLUE => "blue"

end

function show()
    color_map = Dict(Colors.RED => "1", Colors.GREEN => "2", Colors.BLUE => "3")
    a = Colors.GREEN
    if a == Colors.GREEN
        println(join(["green"], " "))
    else

        println(join(["Not green"], " "))
    end
    println(join([length(color_map)], " "))
end

function main()
    show()
end

main()
