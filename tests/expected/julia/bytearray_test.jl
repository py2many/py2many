if abspath(PROGRAM_FILE) == @__FILE__
    values = Vector{UInt8}()
    @assert(isa(values, bytearray) == true)
end
