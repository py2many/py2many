import netscape

error = "Netscape Test Error"
if abspath(PROGRAM_FILE) == @__FILE__
    n = CNetworkCX(netscape)
    rc = Open(n, "http://d|/temp/apyext.html", 0, nothing, 0, nothing)
    if !(rc)
        throw(error("Open method of Netscape failed"))
    end
    while true
        num, str = Read(n, nothing, 0)
        println("Got $(num)$(str)")
        if num == 0
            has_break = true
            break
        end
        if num == -1
            has_break = true
            break
        end
    end
    Close(n)
    println("Done!")
    #Delete Unsupported
    del(n)
    sys.last_type = nothing
    sys.last_value = nothing
    sys.last_traceback = nothing
end
