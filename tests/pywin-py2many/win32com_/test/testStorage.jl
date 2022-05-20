using PyCall
win32api = pyimport("win32api")
pythoncom = pyimport("pythoncom")
using win32com_: storagecon

import win32com_.test.util

abstract type AbstractTestEnum <: Abstractwin32com_.test.util.TestCase end
mutable struct TestEnum <: AbstractTestEnum
end
function testit(self::TestEnum)
    fname, tmp = GetTempFileName(win32api, GetTempPath(win32api), "stg")
    m = storagecon.STGM_READWRITE | storagecon.STGM_SHARE_EXCLUSIVE
    pss = StgOpenStorageEx(
        pythoncom,
        fname,
        m,
        storagecon.STGFMT_FILE,
        0,
        pythoncom.IID_IPropertySetStorage,
    )
    psuser = Create(
        pss,
        pythoncom.FMTID_UserDefinedProperties,
        pythoncom.IID_IPropertySetStorage,
        storagecon.PROPSETFLAG_DEFAULT,
        (storagecon.STGM_READWRITE | storagecon.STGM_CREATE) |
        storagecon.STGM_SHARE_EXCLUSIVE,
    )
    WriteMultiple(psuser, (3, 4), ("hey", "bubba"))
    WritePropertyNames(psuser, (3, 4), ("property3", "property4"))
    expected_summaries = []
    push!(expected_summaries, ("property3", 3, pythoncom.VT_BSTR))
    push!(expected_summaries, ("property4", 4, pythoncom.VT_BSTR))
    psuser = nothing
    pssum = Create(
        pss,
        pythoncom.FMTID_SummaryInformation,
        pythoncom.IID_IPropertySetStorage,
        storagecon.PROPSETFLAG_DEFAULT,
        (storagecon.STGM_READWRITE | storagecon.STGM_CREATE) |
        storagecon.STGM_SHARE_EXCLUSIVE,
    )
    WriteMultiple(
        pssum,
        (storagecon.PIDSI_AUTHOR, storagecon.PIDSI_COMMENTS),
        ("me", "comment"),
    )
    pssum = nothing
    pss = nothing
    pssread = StgOpenStorageEx(
        pythoncom,
        fname,
        storagecon.STGM_READ | storagecon.STGM_SHARE_EXCLUSIVE,
        storagecon.STGFMT_FILE,
        0,
        pythoncom.IID_IPropertySetStorage,
    )
    found_summaries = []
    for psstat in pssread
        ps =
            Open(pssread, psstat[1], storagecon.STGM_READ | storagecon.STGM_SHARE_EXCLUSIVE)
        for p in ps
            p_val = ReadMultiple(ps, (p[2],))[1]
            if p[2] == storagecon.PIDSI_AUTHOR && p_val == "me" ||
               p[2] == storagecon.PIDSI_COMMENTS && p_val == "comment"
                #= pass =#
            else
                fail(self, "Uxexpected property %s/%s" % (p, p_val))
            end
        end
        ps = nothing
        if psstat[1] == pythoncom.FMTID_DocSummaryInformation
            ps = Open(
                pssread,
                pythoncom.FMTID_UserDefinedProperties,
                storagecon.STGM_READ | storagecon.STGM_SHARE_EXCLUSIVE,
            )
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

if abspath(PROGRAM_FILE) == @__FILE__
end
