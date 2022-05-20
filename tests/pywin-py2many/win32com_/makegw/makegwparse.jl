#= Utilities for makegw - Parse a header file to build an interface

 This module contains the core code for parsing a header file describing a
 COM interface, and building it into an "Interface" structure.

 Each Interface has methods, and each method has arguments.

 Each argument knows how to use Py_BuildValue or Py_ParseTuple to
 exchange itself with Python.

 See the @win32com_.makegw@ module for information in building a COM
 interface
 =#
using OrderedCollections
using Printf

abstract type Abstracterror_not_found <: AbstractException end
abstract type Abstracterror_not_supported <: AbstractException end
abstract type AbstractArgFormatter end
abstract type AbstractArgFormatterFloat <: AbstractArgFormatter end
abstract type AbstractArgFormatterShort <: AbstractArgFormatter end
abstract type AbstractArgFormatterLONG_PTR <: AbstractArgFormatter end
abstract type AbstractArgFormatterPythonCOM <: AbstractArgFormatter end
abstract type AbstractArgFormatterBSTR <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterOLECHAR <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterTCHAR <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterIID <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterTime <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterSTATSTG <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterGeneric <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterIDLIST <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterHANDLE <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterLARGE_INTEGER <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterULARGE_INTEGER <: AbstractArgFormatterLARGE_INTEGER end
abstract type AbstractArgFormatterInterface <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterVARIANT <: AbstractArgFormatterPythonCOM end
abstract type AbstractArgFormatterSimple <: AbstractArgFormatter end
abstract type AbstractArgument end
abstract type AbstractMethod end
abstract type AbstractInterface end
mutable struct error_not_found <: Abstracterror_not_found
    msg::String

    error_not_found(msg = "The requested item could not be found") = begin
        super(error_not_found, self).__init__(msg)
        new(msg)
    end
end

mutable struct error_not_supported <: Abstracterror_not_supported
    msg::String

    error_not_supported(msg = "The required functionality is not supported") = begin
        super(error_not_supported, self).__init__(msg)
        new(msg)
    end
end

VERBOSE = 0
DEBUG = 0
mutable struct ArgFormatter <: AbstractArgFormatter
    #= An instance for a specific type of argument.\t Knows how to convert itself =#
    arg
    builtinIndirection
    declaredIndirection
    gatewayMode::Int64
end
function _IndirectPrefix(self::ArgFormatter, indirectionFrom, indirectionTo)::String
    #= Given the indirection level I was declared at (0=Normal, 1=*, 2=**)
            return a string prefix so I can pass to a function with the
            required indirection (where the default is the indirection of the method's param.

            eg, assuming my arg has indirection level of 2, if this function was passed 1
            it would return "&", so that a variable declared with indirection of 1
            can be prefixed with this to turn it into the indirection level required of 2
             =#
    dif = indirectionFrom - indirectionTo
    if dif == 0
        return ""
    elseif dif == -1
        return "&"
    elseif dif == 1
        return "*"
    else
        return "?? (%d)" % (dif,)
        throw(error_not_supported("Can\'t indirect this far - please fix me :-)"))
    end
end

function GetIndirectedArgName(self::ArgFormatter, indirectFrom, indirectionTo)::String
    if indirectFrom === nothing
        indirectFrom = _GetDeclaredIndirection(self) + self.builtinIndirection
    end
    return _IndirectPrefix(self, indirectFrom, indirectionTo) + self.arg.name
end

function GetBuildValueArg(self::ArgFormatter)
    #= Get the argument to be passes to Py_BuildValue =#
    return self.arg.name
end

function GetParseTupleArg(self::ArgFormatter)::String
    #= Get the argument to be passed to PyArg_ParseTuple =#
    if self.gatewayMode != 0
        return GetIndirectedArgName(self, nothing, 1)
    end
    return GetIndirectedArgName(self, self.builtinIndirection, 1)
end

function GetInterfaceCppObjectInfo(self::ArgFormatter)
    #= Provide information about the C++ object used.

            Simple variables (such as integers) can declare their type (eg an integer)
            and use it as the target of both PyArg_ParseTuple and the COM function itself.

            More complex types require a PyObject * declared as the target of PyArg_ParseTuple,
            then some conversion routine to the C++ object which is actually passed to COM.

            This method provides the name, and optionally the type of that C++ variable.
            If the type if provided, the caller will likely generate a variable declaration.
            The name must always be returned.

            Result is a tuple of (variableName, [DeclareType|None|""])
             =#
    return (
        GetIndirectedArgName(
            self,
            self.builtinIndirection,
            self.arg.indirectionLevel + self.builtinIndirection,
        ),
        "%s %s" % (GetUnconstType(self), self.arg.name),
    )
end

function GetInterfaceArgCleanup(self::ArgFormatter)::String
    #= Return cleanup code for C++ args passed to the interface method. =#
    if DEBUG != 0
        return "/* GetInterfaceArgCleanup output goes here: %s */\n" % self.arg.name
    else
        return ""
    end
end

function GetInterfaceArgCleanupGIL(self::ArgFormatter)::String
    #= Return cleanup code for C++ args passed to the interface
            method that must be executed with the GIL held =#
    if DEBUG != 0
        return "/* GetInterfaceArgCleanup (GIL held) output goes here: %s */\n" %
               self.arg.name
    else
        return ""
    end
end

function GetUnconstType(self::ArgFormatter)
    return self.arg.unc_type
end

function SetGatewayMode(self::ArgFormatter)
    self.gatewayMode = 1
end

function _GetDeclaredIndirection(self::ArgFormatter)
    return self.arg.indirectionLevel
    println("declared:$(self.arg.name)$(self.gatewayMode)")
    if self.gatewayMode != 0
        return self.arg.indirectionLevel
    else
        return self.declaredIndirection
    end
end

function DeclareParseArgTupleInputConverter(self::ArgFormatter)::String
    #= Declare the variable used as the PyArg_ParseTuple param for a gateway =#
    if DEBUG != 0
        return "/* Declare ParseArgTupleInputConverter goes here: %s */\n" % self.arg.name
    else
        return ""
    end
end

function GetParsePostCode(self::ArgFormatter)::String
    #= Get a string of C++ code to be executed after (ie, to finalise) the PyArg_ParseTuple conversion =#
    if DEBUG != 0
        return "/* GetParsePostCode code goes here: %s */\n" % self.arg.name
    else
        return ""
    end
end

function GetBuildForInterfacePreCode(self::ArgFormatter)::String
    #= Get a string of C++ code to be executed before (ie, to initialise) the Py_BuildValue conversion for Interfaces =#
    if DEBUG != 0
        return "/* GetBuildForInterfacePreCode goes here: %s */\n" % self.arg.name
    else
        return ""
    end
end

function GetBuildForGatewayPreCode(self::ArgFormatter)::String
    #= Get a string of C++ code to be executed before (ie, to initialise) the Py_BuildValue conversion for Gateways =#
    s = GetBuildForInterfacePreCode(self)
    if DEBUG != 0
        if s[begin:4] == "/* G"
            s = "/* GetBuildForGatewayPreCode goes here: %s */\n" % self.arg.name
        end
    end
    return s
end

function GetBuildForInterfacePostCode(self::ArgFormatter)::String
    #= Get a string of C++ code to be executed after (ie, to finalise) the Py_BuildValue conversion for Interfaces =#
    if DEBUG != 0
        return "/* GetBuildForInterfacePostCode goes here: %s */\n" % self.arg.name
    end
    return ""
end

function GetBuildForGatewayPostCode(self::ArgFormatter)::String
    #= Get a string of C++ code to be executed after (ie, to finalise) the Py_BuildValue conversion for Gateways =#
    s = GetBuildForInterfacePostCode(self)
    if DEBUG != 0
        if s[begin:4] == "/* G"
            s = "/* GetBuildForGatewayPostCode goes here: %s */\n" % self.arg.name
        end
    end
    return s
end

function GetAutoduckString(self::ArgFormatter)
    return "// @pyparm %s|%s||Description for %s" %
           (_GetPythonTypeDesc(self), self.arg.name, self.arg.name)
end

function _GetPythonTypeDesc(self::ArgFormatter)
    #= Returns a string with the description of the type.\t Used for doco purposes =#
    return nothing
end

function NeedUSES_CONVERSION(self::ArgFormatter)::Int64
    #= Determines if this arg forces a USES_CONVERSION macro =#
    return 0
end

mutable struct ArgFormatterFloat <: AbstractArgFormatterFloat
    arg
    gatewayMode
end
function GetFormatChar(self::ArgFormatterFloat)::String
    return "f"
end

function DeclareParseArgTupleInputConverter(self::ArgFormatterFloat)::String
    return "\tdouble dbl%s;\n" % self.arg.name
end

function GetParseTupleArg(self::ArgFormatterFloat)::String
    return "&dbl" + self.arg.name
end

function _GetPythonTypeDesc(self::ArgFormatterFloat)::String
    return "float"
end

function GetBuildValueArg(self::ArgFormatterFloat)::String
    return "&dbl" + self.arg.name
end

function GetBuildForInterfacePreCode(self::ArgFormatterFloat)::String
    return (("\tdbl" + self.arg.name) * " = " + self.arg.name) * ";\n"
end

function GetBuildForGatewayPreCode(self::ArgFormatterFloat)::String
    return (
        (
            ("\tdbl%s = " % self.arg.name) +
            _IndirectPrefix(self, _GetDeclaredIndirection(self), 0)
        ) + self.arg.name
    ) * ";\n"
end

function GetParsePostCode(self::ArgFormatterFloat)::String
    s = "\t"
    if self.gatewayMode
        s = s + _IndirectPrefix(self, _GetDeclaredIndirection(self), 0)
    end
    s = s + self.arg.name
    s = s * (" = (float)dbl%s;\n" % self.arg.name)
    return s
end

mutable struct ArgFormatterShort <: AbstractArgFormatterShort
    arg
    gatewayMode
end
function GetFormatChar(self::ArgFormatterShort)::String
    return "i"
end

function DeclareParseArgTupleInputConverter(self::ArgFormatterShort)::String
    return "\tINT i%s;\n" % self.arg.name
end

function GetParseTupleArg(self::ArgFormatterShort)::String
    return "&i" + self.arg.name
end

function _GetPythonTypeDesc(self::ArgFormatterShort)::String
    return "int"
end

function GetBuildValueArg(self::ArgFormatterShort)::String
    return "&i" + self.arg.name
end

function GetBuildForInterfacePreCode(self::ArgFormatterShort)::String
    return (("\ti" + self.arg.name) * " = " + self.arg.name) * ";\n"
end

function GetBuildForGatewayPreCode(self::ArgFormatterShort)::String
    return (
        (
            ("\ti%s = " % self.arg.name) +
            _IndirectPrefix(self, _GetDeclaredIndirection(self), 0)
        ) + self.arg.name
    ) * ";\n"
end

function GetParsePostCode(self::ArgFormatterShort)::String
    s = "\t"
    if self.gatewayMode
        s = s + _IndirectPrefix(self, _GetDeclaredIndirection(self), 0)
    end
    s = s + self.arg.name
    s = s * (" = i%s;\n" % self.arg.name)
    return s
end

mutable struct ArgFormatterLONG_PTR <: AbstractArgFormatterLONG_PTR
    arg
end
function GetFormatChar(self::ArgFormatterLONG_PTR)::String
    return "O"
end

function DeclareParseArgTupleInputConverter(self::ArgFormatterLONG_PTR)::String
    return "\tPyObject *ob%s;\n" % self.arg.name
end

function GetParseTupleArg(self::ArgFormatterLONG_PTR)::String
    return "&ob" + self.arg.name
end

function _GetPythonTypeDesc(self::ArgFormatterLONG_PTR)::String
    return "int/long"
end

function GetBuildValueArg(self::ArgFormatterLONG_PTR)::String
    return "ob" + self.arg.name
end

function GetBuildForInterfacePostCode(self::ArgFormatterLONG_PTR)::String
    return "\tPy_XDECREF(ob%s);\n" % self.arg.name
end

function DeclareParseArgTupleInputConverter(self::ArgFormatterLONG_PTR)::String
    return "\tPyObject *ob%s;\n" % self.arg.name
end

function GetParsePostCode(self::ArgFormatterLONG_PTR)
    return "\tif (bPythonIsHappy && !PyWinLong_AsULONG_PTR(ob%s, (ULONG_PTR *)%s)) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 2))
end

function GetBuildForInterfacePreCode(self::ArgFormatterLONG_PTR)
    notdirected = GetIndirectedArgName(self, nothing, 1)
    return "\tob%s = PyWinObject_FromULONG_PTR(%s);\n" % (self.arg.name, notdirected)
end

function GetBuildForGatewayPostCode(self::ArgFormatterLONG_PTR)::String
    return "\tPy_XDECREF(ob%s);\n" % self.arg.name
end

mutable struct ArgFormatterPythonCOM <: AbstractArgFormatterPythonCOM
    #= An arg formatter for types exposed in the PythonCOM module =#
    arg
end
function GetFormatChar(self::ArgFormatterPythonCOM)::String
    return "O"
end

function DeclareParseArgTupleInputConverter(self::ArgFormatterPythonCOM)::String
    return "\tPyObject *ob%s;\n" % self.arg.name
end

function GetParseTupleArg(self::ArgFormatterPythonCOM)::String
    return "&ob" + self.arg.name
end

function _GetPythonTypeDesc(self::ArgFormatterPythonCOM)::String
    return "<o Py%s>" % self.arg.type
end

function GetBuildValueArg(self::ArgFormatterPythonCOM)::String
    return "ob" + self.arg.name
end

function GetBuildForInterfacePostCode(self::ArgFormatterPythonCOM)::String
    return "\tPy_XDECREF(ob%s);\n" % self.arg.name
end

function DeclareParseArgTupleInputConverter(self::ArgFormatterPythonCOM)::String
    return "\tPyObject *ob%s;\n" % self.arg.name
end

mutable struct ArgFormatterBSTR <: AbstractArgFormatterBSTR
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterBSTR)::String
    return "<o unicode>"
end

function GetParsePostCode(self::ArgFormatterBSTR)
    return "\tif (bPythonIsHappy && !PyWinObject_AsBstr(ob%s, %s)) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 2))
end

function GetBuildForInterfacePreCode(self::ArgFormatterBSTR)
    notdirected = GetIndirectedArgName(self, nothing, 1)
    return "\tob%s = MakeBstrToObj(%s);\n" % (self.arg.name, notdirected)
end

function GetBuildForInterfacePostCode(self::ArgFormatterBSTR)::Any
    return ("\tSysFreeString(%s);\n" % (self.arg.name,)) +
           GetBuildForInterfacePostCode(ArgFormatterPythonCOM)
end

function GetBuildForGatewayPostCode(self::ArgFormatterBSTR)::String
    return "\tPy_XDECREF(ob%s);\n" % self.arg.name
end

mutable struct ArgFormatterOLECHAR <: AbstractArgFormatterOLECHAR
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterOLECHAR)::String
    return "<o unicode>"
end

function GetUnconstType(self::ArgFormatterOLECHAR)::Any
    if self.arg.type[begin:3] == "LPC"
        return self.arg.type[begin:2] + self.arg.type[4:end]
    else
        return self.arg.unc_type
    end
end

function GetParsePostCode(self::ArgFormatterOLECHAR)
    return "\tif (bPythonIsHappy && !PyWinObject_AsBstr(ob%s, %s)) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 2))
end

function GetInterfaceArgCleanup(self::ArgFormatterOLECHAR)::String
    return "\tSysFreeString(%s);\n" % GetIndirectedArgName(self, nothing, 1)
end

function GetBuildForInterfacePreCode(self::ArgFormatterOLECHAR)
    notdirected = GetIndirectedArgName(self, self.builtinIndirection, 1)
    return "\tob%s = MakeOLECHARToObj(%s);\n" % (self.arg.name, notdirected)
end

function GetBuildForInterfacePostCode(self::ArgFormatterOLECHAR)::Any
    return ("\tCoTaskMemFree(%s);\n" % (self.arg.name,)) +
           GetBuildForInterfacePostCode(ArgFormatterPythonCOM)
end

function GetBuildForGatewayPostCode(self::ArgFormatterOLECHAR)::String
    return "\tPy_XDECREF(ob%s);\n" % self.arg.name
end

mutable struct ArgFormatterTCHAR <: AbstractArgFormatterTCHAR
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterTCHAR)::String
    return "string/<o unicode>"
end

function GetUnconstType(self::ArgFormatterTCHAR)::Any
    if self.arg.type[begin:3] == "LPC"
        return self.arg.type[begin:2] + self.arg.type[4:end]
    else
        return self.arg.unc_type
    end
end

function GetParsePostCode(self::ArgFormatterTCHAR)
    return "\tif (bPythonIsHappy && !PyWinObject_AsTCHAR(ob%s, %s)) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 2))
end

function GetInterfaceArgCleanup(self::ArgFormatterTCHAR)::String
    return "\tPyWinObject_FreeTCHAR(%s);\n" % GetIndirectedArgName(self, nothing, 1)
end

function GetBuildForInterfacePreCode(self::ArgFormatterTCHAR)
    notdirected = GetIndirectedArgName(self, self.builtinIndirection, 1)
    return "\tob%s = PyWinObject_FromTCHAR(%s);\n" % (self.arg.name, notdirected)
end

function GetBuildForInterfacePostCode(self::ArgFormatterTCHAR)::String
    return "// ??? - TCHAR post code\n"
end

function GetBuildForGatewayPostCode(self::ArgFormatterTCHAR)::String
    return "\tPy_XDECREF(ob%s);\n" % self.arg.name
end

mutable struct ArgFormatterIID <: AbstractArgFormatterIID
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterIID)::String
    return "<o PyIID>"
end

function GetParsePostCode(self::ArgFormatterIID)
    return "\tif (!PyWinObject_AsIID(ob%s, &%s)) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, self.arg.name)
end

function GetBuildForInterfacePreCode(self::ArgFormatterIID)
    notdirected = GetIndirectedArgName(self, nothing, 0)
    return "\tob%s = PyWinObject_FromIID(%s);\n" % (self.arg.name, notdirected)
end

function GetInterfaceCppObjectInfo(self::ArgFormatterIID)
    return (self.arg.name, "IID %s" % self.arg.name)
end

mutable struct ArgFormatterTime <: AbstractArgFormatterTime
    arg
    builtinIndirection
    declaredIndirection::Int64

    ArgFormatterTime(arg, builtinIndirection, declaredIndirection = 0) = begin
        if arg.indirectionLevel == 0 && arg.unc_type[begin:2] == "LP"
            arg.unc_type = arg.unc_type[2:end]
            arg.indirectionLevel = arg.indirectionLevel + 1
            builtinIndirection = 0
        end
        ArgFormatterPythonCOM(arg, builtinIndirection, declaredIndirection)
        new(arg, builtinIndirection, declaredIndirection)
    end
end
function _GetPythonTypeDesc(self::ArgFormatterTime)::String
    return "<o PyDateTime>"
end

function GetParsePostCode(self::ArgFormatterTime)
    return "\tif (!PyTime_Check(ob%s)) {\n\t\tPyErr_SetString(PyExc_TypeError, \"The argument must be a PyTime object\");\n\t\tbPythonIsHappy = FALSE;\n\t}\n\tif (!((PyTime *)ob%s)->GetTime(%s)) bPythonIsHappy = FALSE;\n" %
           (
        self.arg.name,
        self.arg.name,
        GetIndirectedArgName(self, self.builtinIndirection, 1),
    )
end

function GetBuildForInterfacePreCode(self::ArgFormatterTime)
    notdirected = GetIndirectedArgName(self, self.builtinIndirection, 0)
    return "\tob%s = new PyTime(%s);\n" % (self.arg.name, notdirected)
end

function GetBuildForInterfacePostCode(self::ArgFormatterTime)::String
    ret = ""
    if (self.builtinIndirection + self.arg.indirectionLevel) > 1
        ret = "\tCoTaskMemFree(%s);\n" % self.arg.name
    end
    return ret * GetBuildForInterfacePostCode(ArgFormatterPythonCOM)
end

mutable struct ArgFormatterSTATSTG <: AbstractArgFormatterSTATSTG
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterSTATSTG)::String
    return "<o STATSTG>"
end

function GetParsePostCode(self::ArgFormatterSTATSTG)
    return "\tif (!PyCom_PyObjectAsSTATSTG(ob%s, %s, 0/*flags*/)) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 1))
end

function GetBuildForInterfacePreCode(self::ArgFormatterSTATSTG)
    notdirected = GetIndirectedArgName(self, nothing, 1)
    return "\tob%s = PyCom_PyObjectFromSTATSTG(%s);\n\t// STATSTG doco says our responsibility to free\n\tif ((%s).pwcsName) CoTaskMemFree((%s).pwcsName);\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 1), notdirected, notdirected)
end

mutable struct ArgFormatterGeneric <: AbstractArgFormatterGeneric
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterGeneric)::String
    return "<o %s>" % self.arg.type
end

function GetParsePostCode(self::ArgFormatterGeneric)
    return "\tif (!PyObject_As%s(ob%s, &%s) bPythonIsHappy = FALSE;\n" %
           (self.arg.type, self.arg.name, GetIndirectedArgName(self, nothing, 1))
end

function GetInterfaceArgCleanup(self::ArgFormatterGeneric)
    return "\tPyObject_Free%s(%s);\n" % (self.arg.type, self.arg.name)
end

function GetBuildForInterfacePreCode(self::ArgFormatterGeneric)
    notdirected = GetIndirectedArgName(self, nothing, 1)
    return "\tob%s = PyObject_From%s(%s);\n" %
           (self.arg.name, self.arg.type, GetIndirectedArgName(self, nothing, 1))
end

mutable struct ArgFormatterIDLIST <: AbstractArgFormatterIDLIST
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterIDLIST)::String
    return "<o PyIDL>"
end

function GetParsePostCode(self::ArgFormatterIDLIST)
    return "\tif (bPythonIsHappy && !PyObject_AsPIDL(ob%s, &%s)) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 1))
end

function GetInterfaceArgCleanup(self::ArgFormatterIDLIST)
    return "\tPyObject_FreePIDL(%s);\n" % (self.arg.name,)
end

function GetBuildForInterfacePreCode(self::ArgFormatterIDLIST)
    notdirected = GetIndirectedArgName(self, nothing, 1)
    return "\tob%s = PyObject_FromPIDL(%s);\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 1))
end

mutable struct ArgFormatterHANDLE <: AbstractArgFormatterHANDLE
    arg
end
function _GetPythonTypeDesc(self::ArgFormatterHANDLE)::String
    return "<o PyHANDLE>"
end

function GetParsePostCode(self::ArgFormatterHANDLE)
    return "\tif (!PyWinObject_AsHANDLE(ob%s, &%s, FALSE) bPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 1))
end

function GetBuildForInterfacePreCode(self::ArgFormatterHANDLE)
    notdirected = GetIndirectedArgName(self, nothing, 1)
    return "\tob%s = PyWinObject_FromHANDLE(%s);\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 0))
end

mutable struct ArgFormatterLARGE_INTEGER <: AbstractArgFormatterLARGE_INTEGER
    arg
end
function GetKeyName(self::ArgFormatterLARGE_INTEGER)::String
    return "LARGE_INTEGER"
end

function _GetPythonTypeDesc(self::ArgFormatterLARGE_INTEGER)::String
    return "<o %s>" % GetKeyName(self)
end

function GetParsePostCode(self::ArgFormatterLARGE_INTEGER)
    return "\tif (!PyWinObject_As%s(ob%s, %s)) bPythonIsHappy = FALSE;\n" %
           (GetKeyName(self), self.arg.name, GetIndirectedArgName(self, nothing, 1))
end

function GetBuildForInterfacePreCode(self::ArgFormatterLARGE_INTEGER)
    notdirected = GetIndirectedArgName(self, nothing, 0)
    return "\tob%s = PyWinObject_From%s(%s);\n" %
           (self.arg.name, GetKeyName(self), notdirected)
end

mutable struct ArgFormatterULARGE_INTEGER <: AbstractArgFormatterULARGE_INTEGER
end
function GetKeyName(self::ArgFormatterULARGE_INTEGER)::String
    return "ULARGE_INTEGER"
end

mutable struct ArgFormatterInterface <: AbstractArgFormatterInterface
    arg
    gatewayMode
end
function GetInterfaceCppObjectInfo(self::ArgFormatterInterface)::Tuple
    return (
        GetIndirectedArgName(self, 1, self.arg.indirectionLevel),
        "%s * %s" % (GetUnconstType(self), self.arg.name),
    )
end

function GetParsePostCode(self::ArgFormatterInterface)
    if self.gatewayMode
        sArg = GetIndirectedArgName(self, nothing, 2)
    else
        sArg = GetIndirectedArgName(self, 1, 2)
    end
    return "\tif (bPythonIsHappy && !PyCom_InterfaceFromPyInstanceOrObject(ob%s, IID_%s, (void **)%s, TRUE /* bNoneOK */))\n\t\t bPythonIsHappy = FALSE;\n" %
           (self.arg.name, self.arg.type, sArg)
end

function GetBuildForInterfacePreCode(self::ArgFormatterInterface)
    return "\tob%s = PyCom_PyObjectFromIUnknown(%s, IID_%s, FALSE);\n" %
           (self.arg.name, self.arg.name, self.arg.type)
end

function GetBuildForGatewayPreCode(self::ArgFormatterInterface)
    sPrefix = _IndirectPrefix(self, _GetDeclaredIndirection(self), 1)
    return "\tob%s = PyCom_PyObjectFromIUnknown(%s%s, IID_%s, TRUE);\n" %
           (self.arg.name, sPrefix, self.arg.name, self.arg.type)
end

function GetInterfaceArgCleanup(self::ArgFormatterInterface)
    return "\tif (%s) %s->Release();\n" % (self.arg.name, self.arg.name)
end

mutable struct ArgFormatterVARIANT <: AbstractArgFormatterVARIANT
    arg
end
function GetParsePostCode(self::ArgFormatterVARIANT)
    return "\tif ( !PyCom_VariantFromPyObject(ob%s, %s) )\n\t\tbPythonIsHappy = FALSE;\n" %
           (self.arg.name, GetIndirectedArgName(self, nothing, 1))
end

function GetBuildForGatewayPreCode(self::ArgFormatterVARIANT)
    notdirected = GetIndirectedArgName(self, nothing, 1)
    return "\tob%s = PyCom_PyObjectFromVariant(%s);\n" % (self.arg.name, notdirected)
end

function GetBuildForGatewayPostCode(self::ArgFormatterVARIANT)::String
    return "\tPy_XDECREF(ob%s);\n" % self.arg.name
end

ConvertSimpleTypes = OrderedDict(
    "BOOL" => ("BOOL", "int", "i"),
    "UINT" => ("UINT", "int", "i"),
    "BYTE" => ("BYTE", "int", "i"),
    "INT" => ("INT", "int", "i"),
    "DWORD" => ("DWORD", "int", "l"),
    "HRESULT" => ("HRESULT", "int", "l"),
    "ULONG" => ("ULONG", "int", "l"),
    "LONG" => ("LONG", "int", "l"),
    "int" => ("int", "int", "i"),
    "long" => ("long", "int", "l"),
    "DISPID" => ("DISPID", "long", "l"),
    "APPBREAKFLAGS" => ("int", "int", "i"),
    "BREAKRESUMEACTION" => ("int", "int", "i"),
    "ERRORRESUMEACTION" => ("int", "int", "i"),
    "BREAKREASON" => ("int", "int", "i"),
    "BREAKPOINT_STATE" => ("int", "int", "i"),
    "BREAKRESUME_ACTION" => ("int", "int", "i"),
    "SOURCE_TEXT_ATTR" => ("int", "int", "i"),
    "TEXT_DOC_ATTR" => ("int", "int", "i"),
    "QUERYOPTION" => ("int", "int", "i"),
    "PARSEACTION" => ("int", "int", "i"),
)
mutable struct ArgFormatterSimple <: AbstractArgFormatterSimple
    #= An arg formatter for simple integer etc types =#
    arg
end
function GetFormatChar(self::ArgFormatterSimple)::Tuple <
         str >
         return ConvertSimpleTypes[self.arg.type][2] end

function _GetPythonTypeDesc(self::ArgFormatterSimple)::Tuple <
         str >
         return ConvertSimpleTypes[self.arg.type][1] end

AllConverters = Dict(
    "const OLECHAR" => (ArgFormatterOLECHAR, 0, 1),
    "WCHAR" => (ArgFormatterOLECHAR, 0, 1),
    "OLECHAR" => (ArgFormatterOLECHAR, 0, 1),
    "LPCOLESTR" => (ArgFormatterOLECHAR, 1, 1),
    "LPOLESTR" => (ArgFormatterOLECHAR, 1, 1),
    "LPCWSTR" => (ArgFormatterOLECHAR, 1, 1),
    "LPWSTR" => (ArgFormatterOLECHAR, 1, 1),
    "LPCSTR" => (ArgFormatterOLECHAR, 1, 1),
    "LPTSTR" => (ArgFormatterTCHAR, 1, 1),
    "LPCTSTR" => (ArgFormatterTCHAR, 1, 1),
    "HANDLE" => (ArgFormatterHANDLE, 0),
    "BSTR" => (ArgFormatterBSTR, 1, 0),
    "const IID" => (ArgFormatterIID, 0),
    "CLSID" => (ArgFormatterIID, 0),
    "IID" => (ArgFormatterIID, 0),
    "GUID" => (ArgFormatterIID, 0),
    "const GUID" => (ArgFormatterIID, 0),
    "const IID" => (ArgFormatterIID, 0),
    "REFCLSID" => (ArgFormatterIID, 0),
    "REFIID" => (ArgFormatterIID, 0),
    "REFGUID" => (ArgFormatterIID, 0),
    "const FILETIME" => (ArgFormatterTime, 0),
    "const SYSTEMTIME" => (ArgFormatterTime, 0),
    "const LPSYSTEMTIME" => (ArgFormatterTime, 1, 1),
    "LPSYSTEMTIME" => (ArgFormatterTime, 1, 1),
    "FILETIME" => (ArgFormatterTime, 0),
    "SYSTEMTIME" => (ArgFormatterTime, 0),
    "STATSTG" => (ArgFormatterSTATSTG, 0),
    "LARGE_INTEGER" => (ArgFormatterLARGE_INTEGER, 0),
    "ULARGE_INTEGER" => (ArgFormatterULARGE_INTEGER, 0),
    "VARIANT" => (ArgFormatterVARIANT, 0),
    "float" => (ArgFormatterFloat, 0),
    "single" => (ArgFormatterFloat, 0),
    "short" => (ArgFormatterShort, 0),
    "WORD" => (ArgFormatterShort, 0),
    "VARIANT_BOOL" => (ArgFormatterShort, 0),
    "HWND" => (ArgFormatterLONG_PTR, 1),
    "HMENU" => (ArgFormatterLONG_PTR, 1),
    "HOLEMENU" => (ArgFormatterLONG_PTR, 1),
    "HICON" => (ArgFormatterLONG_PTR, 1),
    "HDC" => (ArgFormatterLONG_PTR, 1),
    "LPARAM" => (ArgFormatterLONG_PTR, 1),
    "WPARAM" => (ArgFormatterLONG_PTR, 1),
    "LRESULT" => (ArgFormatterLONG_PTR, 1),
    "UINT" => (ArgFormatterShort, 0),
    "SVSIF" => (ArgFormatterShort, 0),
    "Control" => (ArgFormatterInterface, 0, 1),
    "DataObject" => (ArgFormatterInterface, 0, 1),
    "_PropertyBag" => (ArgFormatterInterface, 0, 1),
    "AsyncProp" => (ArgFormatterInterface, 0, 1),
    "DataSource" => (ArgFormatterInterface, 0, 1),
    "DataFormat" => (ArgFormatterInterface, 0, 1),
    "void **" => (ArgFormatterInterface, 2, 2),
    "ITEMIDLIST" => (ArgFormatterIDLIST, 0, 0),
    "LPITEMIDLIST" => (ArgFormatterIDLIST, 0, 1),
    "LPCITEMIDLIST" => (ArgFormatterIDLIST, 0, 1),
    "const ITEMIDLIST" => (ArgFormatterIDLIST, 0, 1),
)
for key in keys(ConvertSimpleTypes)
    AllConverters[key] = (ArgFormatterSimple, 0)
end
function make_arg_converter(arg)::ArgFormatterInterface
    try
        clz = AllConverters[arg.type][0]
        bin = AllConverters[arg.type][1]
        decl = 0
        if length(AllConverters[arg.type]) > 2
            decl = AllConverters[arg.type][2]
        end
        return clz(arg, bin, decl)
    catch exn
        if exn isa KeyError
            if arg.type[1] == "I"
                return ArgFormatterInterface(arg, 0, 1)
            end
            throw(
                error_not_supported(
                    "The type \'%s\' (%s) is unknown." % (arg.type, arg.name),
                ),
            )
        end
    end
end

mutable struct Argument <: AbstractArgument
    #= A representation of an argument to a COM method

        This class contains information about a specific argument to a method.
        In addition, methods exist so that an argument knows how to convert itself
        to/from Python arguments.
         =#
    arrayDecl::Int64
    const_::Int64
    good_interface_names
    indirectionLevel::Int64
    inout
    name
    raw_type
    type_
    unc_type
    regex

    Argument(
        arrayDecl::Int64,
        const_::Int64,
        good_interface_names,
        indirectionLevel::Int64,
        inout,
        name,
        raw_type,
        type_,
        unc_type,
        regex = compile(
            re,
            "/\\* \\[([^\\]]*.*?)] \\*/[ \\t](.*[* ]+)(\\w+)(\\[ *])?[\\),]",
        ),
    ) = new(
        arrayDecl,
        const_,
        good_interface_names,
        indirectionLevel,
        inout,
        name,
        raw_type,
        type_,
        unc_type,
        regex,
    )
end
function BuildFromFile(self::Argument, file)
    #= Parse and build my data from a file

            Reads the next line in the file, and matches it as an argument
            description.  If not a valid argument line, an error_not_found exception
            is raised.
             =#
    line = readline(file)
    mo = search(self.regex, line)
    if !(mo)
        throw(error_not_found)
    end
    self.name = group(mo, 3)
    self.inout = split(group(mo, 1), "][")
    typ = strip(group(mo, 2))
    self.raw_type = typ
    self.indirectionLevel = 0
    if group(mo, 4)
        self.arrayDecl = 1
        try
            pos = rindex(typ, "__RPC_FAR")
            self.indirectionLevel = self.indirectionLevel + 1
            typ = strip(typ[begin:pos])
        catch exn
            if exn isa ValueError
                #= pass =#
            end
        end
    end
    typ = replace(typ, "__RPC_FAR", "")
    while true
        try
            pos = rindex(typ, "*")
            self.indirectionLevel = self.indirectionLevel + 1
            typ = strip(typ[begin:pos])
        catch exn
            if exn isa ValueError
                break
            end
        end
    end
    self.type = typ
    if self.type[begin:6] == "const "
        self.unc_type = self.type[7:end]
    else
        self.unc_type = self.type
    end
    if VERBOSE != 0
        @printf(
            "\t   Arg %s of type %s%s (%s)\n",
            self.name,
            self.type,
            repeat("*", self.indirectionLevel),
            self.inout
        )
    end
end

function HasAttribute(self::Argument, typ)::Bool
    #= Determines if the argument has the specific attribute.

            Argument attributes are specified in the header file, such as
            "[in][out][retval]" etc.  You can pass a specific string (eg "out")
            to find if this attribute was specified for the argument
             =#
    return typ ∈ self.inout
end

function GetRawDeclaration(self::Argument)
    ret = "%s %s" % (self.raw_type, self.name)
    if self.arrayDecl != 0
        ret = ret * "[]"
    end
    return ret
end

mutable struct Method <: AbstractMethod
    #= A representation of a C++ method on a COM interface

        This class contains information about a specific method, as well as
        a list of all @Argument@s
         =#
    args::Vector
    callconv
    good_interface_names
    name
    result
    regex

    Method(
        args::Vector,
        callconv,
        good_interface_names,
        name,
        result,
        regex = compile(re, "virtual (/\\*.*?\\*/ )?(.*?) (.*?) (.*?)\\(\\w?"),
    ) = new(args, callconv, good_interface_names, name, result, regex)
end
function BuildFromFile(self::Method, file)
    #= Parse and build my data from a file

            Reads the next line in the file, and matches it as a method
            description.  If not a valid method line, an error_not_found exception
            is raised.
             =#
    line = readline(file)
    mo = search(self.regex, line)
    if !(mo)
        throw(error_not_found)
    end
    self.name = group(mo, 4)
    self.result = group(mo, 2)
    if self.result != "HRESULT"
        if self.result == "DWORD"
            println("Warning: Old style interface detected - compilation errors likely!")
        else
            @printf("Method %s - Only HRESULT return types are supported.\n", self.name)
        end
        @printf("\t Method %s %s(\n", self.result, self.name)
    end
    while true
        arg = Argument(self.good_interface_names)
        try
            BuildFromFile(arg, file)
            append(self.args, arg)
        catch exn
            if exn isa error_not_found
                break
            end
        end
    end
end

mutable struct Interface <: AbstractInterface
    #= A representation of a C++ COM Interface

        This class contains information about a specific interface, as well as
        a list of all @Method@s
         =#
    base
    methods::Vector
    name
    regex

    Interface(mo, regex = compile(re, "(interface|) ([^ ]*) : public (.*)\$")) = begin
        if VERBOSE
            @printf("Interface %s : public %s\n", name, base)
        end
        new(mo, regex)
    end
end
function BuildMethods(self::Interface, file)
    #= Build all sub-methods for this interface =#
    readline(file)
    readline(file)
    while true
        try
            method = Method([self.name])
            BuildFromFile(method, file)
            append(self.methods, method)
        catch exn
            if exn isa error_not_found
                break
            end
        end
    end
end

function find_interface(interfaceName, file)
    #= Find and return an interface in a file

        Given an interface name and file, search for the specified interface.

        Upon return, the interface itself has been built,
        but not the methods.
         =#
    interface = nothing
    line = readline(file)
    while line
        mo = search(Interface.regex, line)
        if mo
            name = group(mo, 2)
            println(name)
            AllConverters[name] = (ArgFormatterInterface, 0, 1)
            if name == interfaceName
                interface = Interface(mo)
                BuildMethods(interface, file)
            end
        end
        line = readline(file)
    end
    if interface
        return interface
    end
    throw(error_not_found)
end

function parse_interface_info(interfaceName, file)
    #= Find, parse and return an interface in a file

        Given an interface name and file, search for the specified interface.

        Upon return, the interface itself is fully built,
         =#
    try
        return find_interface(interfaceName, file)
    catch exn
        if exn isa re.error
            current_exceptions() != [] ? current_exceptions()[end] : nothing
            println("The interface could not be built, as the regular expression failed!")
        end
    end
end

function test()
    f = readline("d:\\msdev\\include\\objidl.h")
    try
        parse_interface_info("IPersistStream", f)
    finally
        close(f)
    end
end

function test_regex(r, text)
    res = search(r, text, 0)
    if res == -1
        println("** Not found")
    else
        @printf(
            "%d\n%s\n%s\n%s\n%s\n",
            res,
            group(r, 1),
            group(r, 2),
            group(r, 3),
            group(r, 4)
        )
    end
end
