#= A COM Server which exposes the NT Performance monitor in a very rudimentary way

Usage from VB:
\tset ob = CreateObject("Python.PerfmonQuery")
\tfreeBytes = ob.Query("Memory", "Available Bytes")
 =#
using PyCall
pythoncom = pyimport("pythoncom")
using win32com_.server: exception, register
import win32pdhutil
import winerror
abstract type AbstractPerfMonQuery end
mutable struct PerfMonQuery <: AbstractPerfMonQuery
    _public_methods_::Vector{String}
    _reg_class_spec_::String
    _reg_clsid_::String
    _reg_desc_::String
    _reg_progid_::String
    _reg_verprogid_::String

    PerfMonQuery(
        _public_methods_::Vector{String} = ["Query"],
        _reg_class_spec_::String = "win32com_.servers.perfmon.PerfMonQuery",
        _reg_clsid_::String = "{64cef7a0-8ece-11d1-a65a-00aa00125a98}",
        _reg_desc_::String = "Python Performance Monitor query object",
        _reg_progid_::String = "Python.PerfmonQuery",
        _reg_verprogid_::String = "Python.PerfmonQuery.1",
    ) = new(
        _public_methods_,
        _reg_class_spec_,
        _reg_clsid_,
        _reg_desc_,
        _reg_progid_,
        _reg_verprogid_,
    )
end
function Query(self::PerfMonQuery, object, counter, instance = nothing, machine = nothing)
    try
        return GetPerformanceAttributes(win32pdhutil, object, counter, instance, machine)
    catch exn
        let exc = exn
            if exc isa win32pdhutil.error
                throw(Exception(exception, exc.strerror))
            end
        end
        let desc = exn
            if desc isa TypeError
                throw(Exception(exception, desc, winerror.DISP_E_TYPEMISMATCH))
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    println("Registering COM server...")
    UseCommandLine(register, PerfMonQuery)
end
