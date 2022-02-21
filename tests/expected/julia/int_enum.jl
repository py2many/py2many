using SuperEnum

@se Colors begin
    RED = 0
    GREEN = 1
    BLUE = 2

end

@se Permissions begin
    R = 1
    W = 2
    X = 16

end

function show()
    color_map = Dict(Colors.RED => "red", Colors.GREEN => "green", Colors.BLUE => "blue")
    a = Colors.GREEN
    if a == Colors.GREEN
        println(join(["green"], " "))
    else

        println(join(["Not green"], " "))
    end
    b = Permissions.R
    if b == Permissions.R
        println(join(["R"], " "))
    else

        println(join(["Not R"], " "))
    end
    @assert(length(color_map) != 0)
end

function main()
    show()
end

main()
