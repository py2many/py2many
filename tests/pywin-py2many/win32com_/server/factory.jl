using PyCall
pythoncom = pyimport("pythoncom")

function RegisterClassFactories(clsids, flags = nothing, clsctx = nothing)::Vector
    #= Given a list of CLSID, create and register class factories.

        Returns a list, which should be passed to RevokeClassFactories
         =#
    if flags === nothing
        flags = pythoncom.REGCLS_MULTIPLEUSE | pythoncom.REGCLS_SUSPENDED
    end
    if clsctx === nothing
        clsctx = pythoncom.CLSCTX_LOCAL_SERVER
    end
    ret = []
    for clsid in clsids
        if clsid[1] ∉ ["-", "/"]
            factory = MakePyFactory(pythoncom, clsid)
            regId = CoRegisterClassObject(pythoncom, clsid, factory, clsctx, flags)
            push!(ret, (factory, regId))
        end
    end
    return ret
end

function RevokeClassFactories(infos)
    for (factory, revokeId) in infos
        CoRevokeClassObject(pythoncom, revokeId)
    end
end
