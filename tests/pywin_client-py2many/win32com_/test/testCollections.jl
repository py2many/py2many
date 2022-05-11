module testCollections
using PyCall
pywintypes = pyimport("pywintypes")
pythoncom = pyimport("pythoncom")

import win32com.server.util
import win32com.test.util
import win32com.client



import winerror
L = Unicode(pywintypes)
abstract type AbstractTestCase <: Abstractwin32com.test.util.TestCase end

error = "collection test error"
function MakeEmptyEnum()
o = wrap(win32com.server.util, Collection(win32com.server.util))
return Dispatch(win32com.client, o)
end

function MakeTestEnum()
sub = wrap(win32com.server.util, Collection(win32com.server.util, ["Sub1", 2, "Sub3"]))
o = wrap(win32com.server.util, Collection(win32com.server.util, [1, "Two", 3, sub]))
return Dispatch(win32com.client, o)
end

function TestEnumAgainst(o, check)
for i in 0:length(check) - 1
if o(i) != check[i + 1]
throw(error("Using default method gave the incorrect value - %s/%s" % (repr(o(i)), repr(check[i + 1]))))
end
end
for i in 0:length(check) - 1
if Item(o, i) != check[i + 1]
throw(error("Using Item method gave the incorrect value - %s/%s" % (repr(o(i)), repr(check[i + 1]))))
end
end
cmp = []
for s in o
push!(cmp, s)
end
if cmp[begin:length(check)] != check
throw(error("Result after looping isnt correct - %s/%s" % (repr(cmp[begin:length(check)]), repr(check))))
end
for i in 0:length(check) - 1
if o[i + 1] != check[i + 1]
throw(error("Using indexing gave the incorrect value"))
end
end
end

function TestEnum(quiet = nothing)
if quiet === nothing
quiet = !("-v" in append!([PROGRAM_FILE], ARGS))
end
if !(quiet)
println("Simple enum test")
end
o = MakeTestEnum()
check = [1, "Two", 3]
TestEnumAgainst(o, check)
if !(quiet)
println("sub-collection test")
end
sub = o[4]
TestEnumAgainst(sub, ["Sub1", 2, "Sub3"])
Remove(o, Count(o) - 1)
if !(quiet)
println("Remove item test")
end
#Delete Unsupported
del(check)
Remove(o, 1)
TestEnumAgainst(o, check)
if !(quiet)
println("Add item test")
end
Add(o, "New Item")
append(check, "New Item")
TestEnumAgainst(o, check)
if !(quiet)
println("Insert item test")
end
Insert(o, 2, -1)
insert(check, 2, -1)
TestEnumAgainst(o, check)
try
o()
throw(error("default method with no args worked when it shouldnt have!"))
catch exn
 let exc = exn
if exc isa com_error(pythoncom)
if hresult(exc) != winerror.DISP_E_BADPARAMCOUNT
throw(error("Expected DISP_E_BADPARAMCOUNT - got %s" % (exc,)))
end
end
end
end
try
Insert(o, "foo", 2)
throw(error("Insert worked when it shouldnt have!"))
catch exn
 let exc = exn
if exc isa com_error(pythoncom)
if hresult(exc) != winerror.DISP_E_TYPEMISMATCH
throw(error("Expected DISP_E_TYPEMISMATCH - got %s" % (exc,)))
end
end
end
end
try
Remove(o, Count(o))
throw(error("Remove worked when it shouldnt have!"))
catch exn
 let exc = exn
if exc isa com_error(pythoncom)
if hresult(exc) != winerror.DISP_E_BADINDEX
throw(error("Expected DISP_E_BADINDEX - got %s" % (exc,)))
end
end
end
end
if !(quiet)
println("Empty collection test")
end
o = MakeEmptyEnum()
for item in o
throw(error("Empty list performed an iteration"))
end
try
ob = o[2]
throw(error("Empty list could be indexed"))
catch exn
if exn isa IndexError
#= pass =#
end
end
try
ob = o[1]
throw(error("Empty list could be indexed"))
catch exn
if exn isa IndexError
#= pass =#
end
end
try
ob = o(0)
throw(error("Empty list could be indexed"))
catch exn
 let exc = exn
if exc isa com_error(pythoncom)
if hresult(exc) != winerror.DISP_E_BADINDEX
throw(error("Expected DISP_E_BADINDEX - got %s" % (exc,)))
end
end
end
end
end

mutable struct TestCase <: AbstractTestCase

end
function testEnum(self::TestCase)
TestEnum()
end

function main()

end

main()
end