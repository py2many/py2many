#= Utilities for selecting and enumerating the Type Libraries installed on the system
 =#
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
import win32com.gen_py.dialogs.list

import win32com_.ext_modules.win32con as win32con
abstract type AbstractTypelibSpec end
mutable struct TypelibSpec <: AbstractTypelibSpec
    clsid::String
    lcid::Int64
    major
    minor
    dll
    desc
    ver_desc
    flags
end
function __getitem__(self::TypelibSpec, item)
    if item == 0
        return self.ver_desc
    end
    throw(IndexError("Cant index me!"))
end

function __lt__(self::TypelibSpec, other)::Bool
    me = (lower(self.ver_desc || ""), lower(self.desc || ""), self.major, self.minor)
    them = (lower(other.ver_desc || ""), lower(other.desc || ""), other.major, other.minor)
    return me < them
end

function __eq__(self::TypelibSpec, other)
    return lower(self.ver_desc || "") == lower(other.ver_desc || "") &&
           lower(self.desc || "") == lower(other.desc || "") &&
           self.major == other.major &&
           self.minor == other.minor
end

function Resolve(self::TypelibSpec)::Int64
    if self.dll === nothing
        return 0
    end
    tlb = LoadTypeLib(pythoncom, self.dll)
    FromTypelib(self, tlb, nothing)
    return 1
end

function FromTypelib(self::TypelibSpec, typelib, dllName = nothing)
    la = GetLibAttr(typelib)
    self.clsid = string(la[1])
    self.lcid = la[2]
    self.major = la[4]
    self.minor = la[5]
    if dllName
        self.dll = dllName
    end
end

function EnumKeys(root)::Vector
    index = 0
    ret = []
    while true
        try
            item = RegEnumKey(win32api, root, index)
        catch exn
            if exn isa win32api.error
                break
            end
        end
        try
            val = RegQueryValue(win32api, root, item)
        catch exn
            if exn isa win32api.error
                val = ""
            end
        end
        push!(ret, (item, val))
        index = index + 1
    end
    return ret
end

FLAG_RESTRICTED = 1
FLAG_CONTROL = 2
FLAG_HIDDEN = 4
function EnumTlbs(excludeFlags = 0)::Vector
    #= Return a list of TypelibSpec objects, one for each registered library. =#
    key = RegOpenKey(win32api, win32con.HKEY_CLASSES_ROOT, "Typelib")
    iids = EnumKeys(key)
    results = []
    for (iid, crap) in iids
        try
            key2 = RegOpenKey(win32api, key, string(iid))
        catch exn
            if exn isa win32api.error
                continue
            end
        end
        for (version, tlbdesc) in EnumKeys(key2)
            major_minor = split(version, ".", 1)
            if length(major_minor) < 2
                append(major_minor, "0")
            end
            major = major_minor[1]
            minor = major_minor[2]
            key3 = RegOpenKey(win32api, key2, string(version))
            try
                flags = parse(Int, RegQueryValue(win32api, key3, "FLAGS"))
            catch exn
                if exn isa (win32api.error, ValueError)
                    flags = 0
                end
            end
            if (flags & excludeFlags) == 0
                for (lcid, crap) in EnumKeys(key3)
                    try
                        lcid = parse(Int, lcid)
                    catch exn
                        if exn isa ValueError
                            continue
                        end
                    end
                    try
                        key4 = RegOpenKey(win32api, key3, "%s\\win32" % (lcid,))
                    catch exn
                        if exn isa win32api.error
                            try
                                key4 = RegOpenKey(win32api, key3, "%s\\win64" % (lcid,))
                            catch exn
                                if exn isa win32api.error
                                    continue
                                end
                            end
                        end
                    end
                    try
                        dll, typ = RegQueryValueEx(win32api, key4, nothing)
                        if typ == win32con.REG_EXPAND_SZ
                            dll = ExpandEnvironmentStrings(win32api, dll)
                        end
                    catch exn
                        if exn isa win32api.error
                            dll = nothing
                        end
                    end
                    spec = TypelibSpec(iid, lcid, major, minor, flags)
                    spec.dll = dll
                    spec.desc = tlbdesc
                    spec.ver_desc = ((tlbdesc + " (") + version) * ")"
                    push!(results, spec)
                end
            end
        end
    end
    return results
end

function FindTlbsWithDescription(desc)::Vector
    #= Find all installed type libraries with the specified description =#
    ret = []
    items = EnumTlbs()
    for item in items
        if item.desc == desc
            push!(ret, item)
        end
    end
    return ret
end

function SelectTlb(title = "Select Library", excludeFlags = 0)::Vector
    #= Display a list of all the type libraries, and select one.   Returns None if cancelled =#
    items = EnumTlbs(excludeFlags)
    for i in items
        i.major = parse(Int, i.major)
        i.minor = parse(Int, i.minor)
    end
    sort(items)
    rc = SelectFromLists(win32com.gen_py.dialogs.list, title, items, ["Type Library"])
    if rc === nothing
        return nothing
    end
    return items[rc+1]
end

if abspath(PROGRAM_FILE) == @__FILE__
    println(SelectTlb().__dict__)
end
