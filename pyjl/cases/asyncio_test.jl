
#[async]
function nested()
    return @async 42
end

function test_channel()
    channel = Channel(1)
    put!(channel, 42);
    return channel
end

#[async]
function async_main()
    @assert(take!(test_channel()) == 42)
    println("OK");
end

function main()
    async_main();
end

main()
