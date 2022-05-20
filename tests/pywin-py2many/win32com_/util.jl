#= General utility functions common to client and server.

  This module contains a collection of general purpose utility functions.
 =#
using PyCall
win32api = pyimport("win32api")
pythoncom = pyimport("pythoncom")

import win32con
function IIDToInterfaceName(iid)::String
    #= Converts an IID to a string interface name.

        Used primarily for debugging purposes, this allows a cryptic IID to
        be converted to a useful string name.  This will firstly look for interfaces
        known (ie, registered) by pythoncom.  If not known, it will look in the
        registry for a registered interface.

        iid -- An IID object.

        Result -- Always a string - either an interface name, or '<Unregistered interface>'
         =#
    try
        return pythoncom.ServerInterfaces[iid+1]
    catch exn
        if exn isa KeyError
            try
                try
                    return RegQueryValue(
                        win32api,
                        win32con.HKEY_CLASSES_ROOT,
                        "Interface\\%s" % iid,
                    )
                catch exn
                    if exn isa win32api.error
                        #= pass =#
                    end
                end
            catch exn
                if exn isa ImportError
                    #= pass =#
                end
            end
            return string(iid)
        end
    end
end
