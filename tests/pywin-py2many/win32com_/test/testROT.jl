using PyCall
pythoncom = pyimport("pythoncom")

import win32com_.test.util
import winerror
abstract type AbstractTestROT <: Abstractwin32com_.test.util.TestCase end
mutable struct TestROT <: AbstractTestROT
end
function testit(self::TestROT)
    ctx = CreateBindCtx(pythoncom)
    rot = GetRunningObjectTable(pythoncom)
    num = 0
    for mk in rot
        name = GetDisplayName(mk, ctx, nothing)
        num += 1
        try
            for sub in mk
                num += 1
            end
        catch exn
            let exc = exn
                if exc isa pythoncom.com_error
                    if exc.hresult != winerror.E_NOTIMPL
                        error()
                    end
                end
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
end
