if abspath(PROGRAM_FILE) == @__FILE__
    @assert(b"foo" != b"bar")
    @assert(b"\"" == b"\"")
    @assert(b"'" == b"'")
    @assert(b"\xbbfoo" == b"\xbbfoo")
    println("OK")
end
