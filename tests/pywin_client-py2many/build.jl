#= Contains knowledge to build a COM object definition.

This module is used by both the @dynamic@ and @makepy@ modules to build
all knowledge of a COM object.

This module contains classes which contain the actual knowledge of the object.
This include parameter and return type information, the COM dispid and CLSID, etc.

Other modules may use this information to generate .py files, use the information
dynamically, or possibly even generate .html documentation for objects.
 =#

import string
using keyword: iskeyword
import pythoncom
using pywintypes: TimeType
import winerror
import Dates
function _makeDocString(s)
if version_info(sys) < (3,)
s = Vector{UInt8}(s)
end
return repr(s)
end

error = "PythonCOM.Client.Build error"
function _BuildArgList(fdesc, names)::Union[str,Any]
numArgs = max(fdesc[7], length(fdesc[3]))
names = collect(names)
while nothing in names
i = index(names, nothing)
names[i + 1] = "arg%d" % (i,)
end
names = collect(map(MakePublicAttributeName, names[2:numArgs + 1]))
name_num = 0
while length(names) < numArgs
append(names, "arg%d" % (length(names),))
end
for i in 0:5:length(names) - 1
names[i + 1] = names[i + 1] + "\n\t\t\t"
end
return "," + join(names, ", ")
end

valid_identifier_chars = (string.ascii_letters + string.digits) + "_"
function demunge_leading_underscores(className)::Any
i = 0
while className[i + 1] == "_"
i += 1
end
@assert(i >= 2)
return className[i:end] + className[begin:i - 1]
end

function MakePublicAttributeName(className, is_global = false)::Any
if className[begin:2] == "__"
return demunge_leading_underscores(className)
elseif className == "None"
className = "NONE"
elseif iskeyword(className)
ret = capitalize(className)
elseif ret == className
ret = upper(ret)
return ret
elseif is_global && hasattr(__builtins__, className)
ret = capitalize(className)
elseif ret == className
ret = upper(ret)
return ret
end
return join([char for char in className if char in valid_identifier_chars ], "")
end

function MakeDefaultArgRepr(defArgVal)::Union[str,Any]
try
inOut = defArgVal[2]
catch exn
if exn isa IndexError
inOut = pythoncom.PARAMFLAG_FIN
end
end
if inOut & pythoncom.PARAMFLAG_FHASDEFAULT
val = defArgVal[3]
if isa(val, datetime.datetime)
return repr(tuple(utctimetuple(val)))
end
if type_(val) == TimeType
year = year(val)
month = month(val)
day = day(val)
hour = hour(val)
minute = minute(val)
second = second(val)
msec = msec(val)
return "pywintypes.Time((%(year)d, %(month)d, %(day)d, %(hour)d, %(minute)d, %(second)d,0,0,0,%(msec)d))" % locals()
end
return repr(val)
end
return nothing
end

function BuildCallList(fdesc, names, defNamedOptArg, defNamedNotOptArg, defUnnamedArg, defOutArg, is_comment = false)::String
numArgs = length(fdesc[3])
numOptArgs = fdesc[7]
strval = ""
if numOptArgs == -1
firstOptArg = numArgs
numArgs = numArgs - 1
else
firstOptArg = numArgs - numOptArgs
end
for arg in 0:numArgs - 1
try
argName = names[arg + 2]
namedArg = argName != nothing
catch exn
if exn isa IndexError
namedArg = 0
end
end
if !(namedArg)
argName = "arg%d" % arg
end
thisdesc = fdesc[3][arg + 1]
defArgVal = MakeDefaultArgRepr(thisdesc)
if defArgVal === nothing
if (thisdesc[2] & (pythoncom.PARAMFLAG_FOUT | pythoncom.PARAMFLAG_FIN)) == pythoncom.PARAMFLAG_FOUT
defArgVal = defOutArg
elseif namedArg
elseif arg >= firstOptArg
defArgVal = defNamedOptArg
else
defArgVal = defNamedNotOptArg
else
defArgVal = defUnnamedArg
end
end
argName = MakePublicAttributeName(argName)
if ((arg + 1) % 5) == 0
strval = strval * "\n"
if is_comment
strval = strval * "#"
end
strval = strval * "\t\t\t"
end
strval = strval * ", " + argName
if defArgVal
strval = strval * "=" + defArgVal
end
end
if numOptArgs == -1
strval = strval * ", *" + names[end]
end
return strval
end

function main()
println("Use \'makepy.py\' to generate Python code - this module is just a helper")
end

main()
