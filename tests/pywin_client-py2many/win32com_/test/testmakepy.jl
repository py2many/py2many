module testmakepy
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")



import glob

import win32com.test.util
using win32com.client: makepy, selecttlb, gencache

import winerror
function TestBuildAll(verbose = 1)::Int64
num = 0
tlbInfos = EnumTlbs(selecttlb)
for info in tlbInfos
if verbose
@printf("%s (%s)", (desc(info), dll(info)))
end
try
GenerateFromTypeLibSpec(makepy, info)
num += 1
catch exn
 let details = exn
if details isa com_error(pythoncom)
if hresult(details) not in [winerror.TYPE_E_CANTLOADLIBRARY, winerror.TYPE_E_LIBNOTREGISTERED]
println("** COM error on", desc(info))
println(details)
end
end
end
if exn isa KeyboardInterrupt
println("Interrupted!")
throw(KeyboardInterrupt)
end
println("Failed:", desc(info))
current_exceptions() != [] ? current_exceptions()[end] : nothing
end
if makepy.bForDemandDefault
tinfo = (clsid(info), lcid(info), major(info), minor(info))
mod = EnsureModule(gencache, clsid(info), lcid(info), major(info), minor(info))
for name in keys(mod.NamesToIIDMap)
GenerateChildFromTypeLibSpec(makepy, name, tinfo)
end
end
end
return num
end

function TestAll(verbose = 0)
num = TestBuildAll(verbose)
println("Generated and imported", num, "modules")
CheckClean(win32com.test.util)
end

function main()
TestAll("-q" not in append!([PROGRAM_FILE], ARGS))
end

main()
end