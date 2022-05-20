#= Python.Interpreter COM Server

  This module implements a very very simple COM server which
  exposes the Python interpreter.

  This is designed more as a demonstration than a full blown COM server.
  General functionality and Error handling are both limited.

  To use this object, ensure it is registered by running this module
  from Python.exe.  Then, from Visual Basic, use "CreateObject('Python.Interpreter')",
  and call its methods!
 =#
import win32com_.server.register
using win32com_.server.exception: Exception
import winerror
abstract type AbstractInterpreter end
mutable struct Interpreter <: AbstractInterpreter
    #= The interpreter object exposed via COM =#
    dict::Dict
    _public_methods_::Vector{String}
    _reg_class_spec_::String
    _reg_clsid_::String
    _reg_desc_::String
    _reg_progid_::String
    _reg_verprogid_::String

    Interpreter(
        dict::Dict,
        _public_methods_::Vector{String} = ["Exec", "Eval"],
        _reg_class_spec_::String = "win32com_.servers.interp.Interpreter",
        _reg_clsid_::String = "{30BD3490-2632-11cf-AD5B-524153480001}",
        _reg_desc_::String = "Python Interpreter",
        _reg_progid_::String = "Python.Interpreter",
        _reg_verprogid_::String = "Python.Interpreter.2",
    ) = new(
        dict,
        _public_methods_,
        _reg_class_spec_,
        _reg_clsid_,
        _reg_desc_,
        _reg_progid_,
        _reg_verprogid_,
    )
end
function Eval(self::Interpreter, exp)
    #= Evaluate an expression. =#
    if type_(exp) != str
        throw(Exception("Must be a string", winerror.DISP_E_TYPEMISMATCH))
    end
    return eval(string(exp), self.dict)
end

function Exec(self::Interpreter, exp)
    #= Execute a statement. =#
    if type_(exp) != str
        throw(Exception("Must be a string", winerror.DISP_E_TYPEMISMATCH))
    end
    exec(string(exp), self.dict)
end

function Register()
    return UseCommandLine(win32com_.server.register, Interpreter)
end

if abspath(PROGRAM_FILE) == @__FILE__
    println("Registering COM server...")
    Register()
end
