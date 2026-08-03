function main()
    @assert(b"foo" != b"bar")
    @assert(b"\"" == b"\"")
    @assert(b"'" == b"'")
    @assert(b"\xbbfoo" == b"\xbbfoo")
    println(join(["OK"], " "))
end

main()
