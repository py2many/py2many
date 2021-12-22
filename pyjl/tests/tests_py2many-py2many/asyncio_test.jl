
#[async]
function nested()::Int64
return 42
end

#[async]
function async_main()
@assert(await!(nested()) == 42)
println("OK");
end

function main()
run(asyncio, async_main());
end

main()
