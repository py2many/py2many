
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
    task_trange = @async for i ∈ 1:n
      put!(c, i)
    end
    task_trange = @async for i ∈ 1:n
        put!(c, i+1)
    end
    bind(c, task_trange)
end

function trange_while()
    c = Channel{Int}(1)
    i = 0
    task_trange = @async while i < 2
        put!(c, i+1)
        i+=1
    end
    bind(c, task_trange)
end

function run_test()
    channel = test_channel()
    take!(channel)
    # for i in channel
        
    # end
    a = trange(1)
    println(take!(a))
    println(take!(a))

    b = trange_while()
    println(take!(b))
    println(take!(b))
end

run_test()
