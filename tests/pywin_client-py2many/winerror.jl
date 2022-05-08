pythoncom = pyimport("pythoncom")
abstract type Abstract_WinError end
mutable struct _WinError <: Abstract_WinError
    code2name::Any
    namespace::Any

    _WinError() = begin
        for (code, name) in self.code2name.iteritems()
            namespace[name] = code
        end
        new()
    end
end
function get_name(self::Abstract_WinError, code)
    return self.code2name[code+1]
end

winerror = _WinError()
