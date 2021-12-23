
#[async]
function nested()::Int64
return 42
end

#[async]
function async_main()
@assert(wait(nested()) == 42)
println("OK");
end

function main()::Int64
run(asyncio, async_main());
end

main()
