if abspath(PROGRAM_FILE) == @__FILE__
    values_ = Vector{UInt8}()
    @assert(isa(values_, Vector{UInt8}) == true)
end
