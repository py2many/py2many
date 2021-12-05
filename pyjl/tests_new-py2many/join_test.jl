struct Hello
end
function why(self::Hello)::String
return "ola"
end


function main()
println(join([why(Hello()), "adeus"], " "));
end

main()
