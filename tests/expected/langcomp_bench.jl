
function test_python(iterations::Int64)
    iteration = 0
    total = float(0.0)
    array_length = 1000
    array::Vector{Int64} = [i for i = 0:array_length-1]
    println("iterations $(iterations)")
    while iteration < iterations
        innerloop = 0
        while innerloop < 100
            total += array[(iteration+innerloop)%array_length+1]
            innerloop += 1
        end
        iteration += 1
    end
    if total == 15150
        println("OK")
    end
    empty!(array)
end

if abspath(PROGRAM_FILE) == @__FILE__
    test_python(3)
end
