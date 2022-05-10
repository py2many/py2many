module testWMI
using win32com.client: GetObject
import win32com.test.util

abstract type AbstractSimple <: Abstractwin32com.test.util.TestCase end
mutable struct Simple <: AbstractSimple

end
function testit(self::Simple)
cses = InstancesOf(GetObject("WinMgMts:"), "Win32_Process")
vals = []
for cs in cses
val = Value(cs.Properties_("Caption"))
push!(vals, val)
end
assertFalse(self, length(vals) < 5, "We only found %d processes!" % length(vals))
end

function main()

end

main()
end