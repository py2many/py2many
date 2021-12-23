# Possible solution to handle async

#[async]
function nested()
    nested_channel = Channel(1)
    put!(nested_channel, 42)
    close(nested_channel)
    return nested_channel
end
    
#[async]
function async_main()
    @assert(take!(nested()) == 42)
    println("OK");
end

function main()
    async_main()
    # run(asyncio, async_main());
end
    
main()
    