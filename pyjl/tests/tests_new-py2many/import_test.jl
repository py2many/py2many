import Dates as dt
import JSON as js
include("class_scopes.jl")
abstract type AbstractScopeExtension <: AbstractScopeTest end
struct ScopeExtension <: AbstractScopeExtension 
id::String
end
function __init__(self::AbstractScopeExtension, id::String)::None
self.id::String = id
end

function test2(self::AbstractScopeExtension)::String
return "test2"
end

function main()
sc_ext = ScopeExtension("1")
@assert(test(sc_ext) == "test")
@assert(test2(sc_ext) == "test2")
end

main()
