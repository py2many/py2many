module testExchange
using Printf
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
import win32con
import win32com.client
using util: CheckClean
using win32com.client: gencache, constants


ammodule = nothing
function GetDefaultProfileName()
try
key = RegOpenKey(win32api, win32con.HKEY_CURRENT_USER, "Software\\Microsoft\\Windows NT\\CurrentVersion\\Windows Messaging Subsystem\\Profiles")
try
return RegQueryValueEx(win32api, key, "DefaultProfile")[1]
finally
Close(key)
end
catch exn
if exn isa error(win32api)
return nothing
end
end
end

function DumpFolder(folder, indent = 0)
println(" "*indent, Name(folder))
folders = Folders(folder)
folder = GetFirst(folders)
while folder
DumpFolder(folder, indent + 1)
folder = GetNext(folders)
end
end

function DumpFolders(session)
try
infostores = InfoStores(session)
catch exn
if exn isa AttributeError
store = DefaultStore(session)
folder = GetRootFolder(store)
DumpFolder(folder)
return
end
end
println(infostores)
@printf("There are %d infostores", Count(infostores))
for i in 0:Count(infostores) - 1
infostore = infostores[i + 2]
println("Infostore = ", Name(infostore))
try
folder = RootFolder(infostore)
catch exn
 let details = exn
if details isa com_error(pythoncom)
hr, msg, exc, arg = details
if exc && exc[end] == -2147221219
println("This info store is currently not available")
continue;
end
end
end
end
DumpFolder(folder)
end
end

PropTagsById = Dict()
if ammodule
for (name, val) in items(ammodule.constants.__dict__)
PropTagsById[val + 1] = name
end
end
function TestAddress(session)
#= pass =#
end

function TestUser(session)
ae = CurrentUser(session)
fields = getattr(ae, "Fields", [])
@printf("User has %d fields", length(fields))
for f in 0:length(fields) - 1
field = fields[f + 2]
try
id = PropTagsById[ID(field) + 1]
catch exn
if exn isa KeyError
id = ID(field)
end
end
@printf("%s/%s=%s", (Name(field), id, Value(field)))
end
end

function test()
oldcwd = getcwd(os)
try
session = EnsureDispatch(gencache, "MAPI.Session")
try
Logon(session, GetDefaultProfileName())
catch exn
 let details = exn
if details isa com_error(pythoncom)
println("Could not log on to MAPI:", details)
return
end
end
end
catch exn
if exn isa error(pythoncom)
app = EnsureDispatch(gencache, "Outlook.Application")
session = Session(app)
end
end
try
TestUser(session)
TestAddress(session)
DumpFolders(session)
finally
Logoff(session)
chdir(os, oldcwd)
end
end

function main()
test()
CheckClean()
end

main()
end