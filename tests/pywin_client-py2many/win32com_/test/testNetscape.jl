module testNetscape
import netscape

error = "Netscape Test Error"
function main()
n = CNetworkCX(netscape)
rc = Open(n, "http://d|/temp/apyext.html", 0, nothing, 0, nothing)
if !(rc)
throw(error("Open method of Netscape failed"))
end
while true
num, str = Read(n, nothing, 0)
println("Got ", num, str)
if num == 0
break;
end
if num == -1
break;
end
end
Close(n)
println("Done!")
#Delete Unsupported
del(n)
last_type(sys) = nothing
last_value(sys) = nothing
last_traceback(sys) = nothing
end

main()
end