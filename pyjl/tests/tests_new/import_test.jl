abstract type AbstractScopeExtension end
import Dates as dt
import JSON as js
using class_scopes: ScopeTest
struct ScopeExtension::AbstractScopeExtension 
id::String
end

function main()
sc_ext = ScopeExtension(1)
test(sc_ext);
end

main()
