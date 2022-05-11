module testStorage
using PyCall
pythoncom = pyimport("pythoncom")
win32api = pyimport("win32api")
using win32com: storagecon

import win32com.test.util

abstract type AbstractTestEnum <: Abstractwin32com.test.util.TestCase end
mutable struct TestEnum <: AbstractTestEnum

end
function testit(self::TestEnum)
fname, tmp = GetTempFileName(win32api, GetTempPath(win32api), "stg")
m = storagecon.STGM_READWRITE | storagecon.STGM_SHARE_EXCLUSIVE
pss = StgOpenStorageEx(pythoncom, fname, m, storagecon.STGFMT_FILE, 0, IID_IPropertySetStorage(pythoncom))
psuser = Create(pss, FMTID_UserDefinedProperties(pythoncom), IID_IPropertySetStorage(pythoncom), storagecon.PROPSETFLAG_DEFAULT, (storagecon.STGM_READWRITE | storagecon.STGM_CREATE) | storagecon.STGM_SHARE_EXCLUSIVE)
WriteMultiple(psuser, (3, 4), ("hey", "bubba"))
WritePropertyNames(psuser, (3, 4), ("property3", "property4"))
expected_summaries = []
push!(expected_summaries, ("property3", 3, VT_BSTR(pythoncom)))
push!(expected_summaries, ("property4", 4, VT_BSTR(pythoncom)))
psuser = nothing
pssum = Create(pss, FMTID_SummaryInformation(pythoncom), IID_IPropertySetStorage(pythoncom), storagecon.PROPSETFLAG_DEFAULT, (storagecon.STGM_READWRITE | storagecon.STGM_CREATE) | storagecon.STGM_SHARE_EXCLUSIVE)
WriteMultiple(pssum, (storagecon.PIDSI_AUTHOR, storagecon.PIDSI_COMMENTS), ("me", "comment"))
pssum = nothing
pss = nothing
pssread = StgOpenStorageEx(pythoncom, fname, storagecon.STGM_READ | storagecon.STGM_SHARE_EXCLUSIVE, storagecon.STGFMT_FILE, 0, IID_IPropertySetStorage(pythoncom))
found_summaries = []
for psstat in pssread
ps = Open(pssread, psstat[1], storagecon.STGM_READ | storagecon.STGM_SHARE_EXCLUSIVE)
for p in ps
p_val = ReadMultiple(ps, (p[2],))[1]
if p[2] == storagecon.PIDSI_AUTHOR && p_val == "me" || p[2] == storagecon.PIDSI_COMMENTS && p_val == "comment"
#= pass =#
else
fail(self, "Uxexpected property %s/%s" % (p, p_val))
end
end
ps = nothing
if psstat[1] == FMTID_DocSummaryInformation(pythoncom)
ps = Open(pssread, FMTID_UserDefinedProperties(pythoncom), storagecon.STGM_READ | storagecon.STGM_SHARE_EXCLUSIVE)
for p in ps
push!(found_summaries, p)
end
ps = nothing
end
end
psread = nothing
sort(expected_summaries)
sort(found_summaries)
assertEqual(self, expected_summaries, found_summaries)
end

function main()

end

main()
end