module exception
#= Exception Handling

 Exceptions

\t To better support COM exceptions, the framework allows for an instance to be
\t raised.  This instance may have a certain number of known attributes, which are
\t translated into COM exception details.
\t
\t This means, for example, that Python could raise a COM exception that includes details
\t on a Help file and location, and a description for the user.
\t
\t This module provides a class which provides the necessary attributes.

 =#
using PyCall
pythoncom = pyimport("pythoncom")

abstract type AbstractCOMException end
mutable struct COMException <: AbstractCOMException
    #= An Exception object that is understood by the framework.

        If the framework is presented with an exception of type class,
        it looks for certain known attributes on this class to provide rich
        error information to the caller.

        It should be noted that the framework supports providing this error
        information via COM Exceptions, or via the ISupportErrorInfo interface.

        By using this class, you automatically provide rich error information to the
        server.
         =#
    description::Any
    helpfile::Any
    scode::Any
    source::Any
    desc::Any
    helpContext::Any
    helpcontext::Any
    hresult::Any

    COMException(
        description = nothing,
        scode = nothing,
        source = nothing,
        helpfile = nothing,
        helpContext = nothing,
        desc = nothing,
        hresult = nothing,
        helpcontext = helpContext,
    ) = begin
        if scode && scode != 1
            if scode >= -32768 && scode < 32768
                scode = -2147024896 | (scode & 65535)
            end
        end
        if scode == 1 && !(self.description)
            self.description = "S_FALSE"
        elseif scode && !(self.description)
            self.description = pythoncom.GetScodeString(scode)
        end
        pythoncom.com_error.__init__(self, scode, self.description, nothing, -1)
        new(description, scode, source, helpfile, helpContext, desc, hresult, helpcontext)
    end
end
function __repr__(self::COMException)
    return "<COM Exception - scode=%s, desc=%s>" % (self.scode, self.description)
end

Exception = COMException
function IsCOMException(t = nothing)::Bool
    if t === nothing
        t = exc_info(sys)[1]
    end
    try
        return t <: com_error(pythoncom)
    catch exn
        if exn isa TypeError
            return t == com_error(pythoncon)
        end
    end
end

function IsCOMServerException(t = nothing)::Int64
    if t === nothing
        t = exc_info(sys)[1]
    end
    try
        return t <: COMException
    catch exn
        if exn isa TypeError
            return 0
        end
    end
end

end
