using PyEnum

@pyenum Colors::String begin
    RED
    GREEN
    BLUE
end
function show()
    color_map = Dict(Colors.RED => "1", Colors.GREEN => "2", Colors.BLUE => "3")
    a = Colors.GREEN
    if a == Colors.GREEN
        println("green")
    else

        println("Not green")


    end
    println(length(color_map))
end

function main()
    show()
end

main()
