using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
win32ui = pyimport("win32ui")

import win32com_.client
include("win32com_/client/gencache.jl")
import win32con
import string

g_iniName = "Mssccprj.scc"
g_sourceSafe = nothing
function FindVssProjectInfo(fullfname)
#= Looks up the file system for an INI file describing the project.

    Looking up the tree is for ni style packages.

    Returns (projectName, pathToFileName) where pathToFileName contains
    the path from the ini file to the actual file.
     =#
path, fnameonly = split(os.path, fullfname)
origPath = path
project = ""
retPaths = [fnameonly]
while !(project)
iniName = join
database = GetProfileVal(win32api, "Python", "Database", "", iniName)
project = GetProfileVal(win32api, "Python", "Project", "", iniName)
if project
has_break = true
break;
end
path, addpath = split(os.path, path)
if !(addpath)
has_break = true
break;
end
insert(retPaths, 0, addpath)
end
if !(project)
MessageBox(win32ui, "%s\r\n\r\nThis directory is not configured for Python/VSS" % origPath)
return
end
return (project, join(retPaths, "/"), database)
end

function CheckoutFile(fileName)::Int64
global g_sourceSafe
ok = 0
try
mod = EnsureModule(win32com_.client.gencache, "{783CD4E0-9D54-11CF-B8EE-00608CC9A71F}", 0, 5, 0)
if mod === nothing
MessageBox(win32ui, "VSS does not appear to be installed.  The TypeInfo can not be created")
return ok
end
rc = FindVssProjectInfo(fileName)
if rc === nothing
return
end
project, vssFname, database = rc
if g_sourceSafe === nothing
g_sourceSafe = Dispatch(win32com_.client, "SourceSafe")
if !(database)
database = pythoncom.Missing
end
Open(g_sourceSafe, database, pythoncom.Missing, pythoncom.Missing)
end
item = VSSItem(g_sourceSafe, "\$/%s/%s" % (project, vssFname))
Checkout(item, nothing, fileName)
ok = 1
catch exn
 let exc = exn
if exc isa pythoncom.com_error
MessageBox(win32ui, exc.strerror, "Error checking out file")
end
end
typ, val, tb = exc_info(sys)
current_exceptions() != [] ? current_exceptions()[end] : nothing
MessageBox(win32ui, "%s - %s" % (string(typ), string(val)), "Error checking out file")
tb = nothing
end
return ok
end
