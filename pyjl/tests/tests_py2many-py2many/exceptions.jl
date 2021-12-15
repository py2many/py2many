function show()
try
throw(Exception("foo"))
catch exn
 let e = exn
if e isa Exception
println("caught");
end
end
finally
println("Finally");
end
try
(3/0);
catch exn
if exn isa ZeroDivisionError
println("OK");
end
end
try
throw(Exception("foo"))
catch exn
println("Got it");
end
end

function main()
show();
end

main()
