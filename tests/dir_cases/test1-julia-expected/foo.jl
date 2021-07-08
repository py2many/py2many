using bar: bar1
using baz: baz1
function main()
    x = bar1()
    y = baz1()
    @assert(x == 0)
    @assert(y == "foo")
end

main()
