

function mult_int_and_string()::Union[String,int]
a::Int64 = 2
return repeat("test",a)
end

function main()
@assert(mult_int_and_string() == "testtest")
println("Ok");
end

main()
