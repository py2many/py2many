
function test_channel()
    taskref = Ref{Task}();
    channel = Channel(2)
    # task = @async foreach(i->put!(channel, i), 1:4);
    # bind(channel, task)
    put!(channel, 1);
    put!(channel, 2);
    # put!(channel, 2);
    return channel
end

function trange(n::Int)
    c = Channel{Int}(1)
    task = @async for i ∈ 1:n
      put!(c, i)
    end
    bind(c, task)
end

function run_test()
    channel = test_channel()
    take!(channel)
    # for i in channel
        
    # end
    a = trange(1000)
    print(take!(a))
    print(take!(a))
end

run_test()
